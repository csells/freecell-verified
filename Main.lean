import FreeCell
import Lean.Data.Json

open FreeCell Lean

def usage : String := "freecell — verified standard FreeCell solver

Usage:
  freecell solve  (--deal N | --position FILE) [options]
  freecell verify (--deal N | --position FILE) CERTIFICATE [--json]
  freecell deal N
  freecell deals FROM TO
  freecell help

Positions:
  --deal N          Microsoft deal N, 1 ≤ N ≤ 32000
  --position FILE   a position file ('-' for standard input); see README

Solve options:
  --max-positions N   give up (unknown) after visiting more than N positions
                      (default 10000000, roughly 4 GB; 'unlimited' removes the cap)
  --time-limit SECS   give up (unknown) after SECS seconds of search
  --cancel-file PATH  give up (unknown) once PATH exists
  --proposer-budget N positions the untrusted win proposer may expand (default 2000000)
  --reference-only    skip the untrusted win proposer; use only the proved search
  --certificate FILE  write the evidence to a new FILE and re-verify it from disk
  --moves             print the winning moves
  --json              machine-readable output on standard output

--max-positions bounds the proposer and the reference search together; a phase
may overshoot it by one position's successors. Each visited position costs
about 400 bytes, so an unlimited search can exhaust the machine's memory. Limits are checked between
batches of work, and the time limit does not cover writing a certificate.

Exit status: 0 decided (or certificate accepted), 3 unknown,
4 certificate rejected, 2 usage or input error, 1 runtime failure
(for example an unwritable certificate path).
"

def maxDeal : Nat := 32000

/-- Default position cap, so an unattended search cannot exhaust memory (about 400 bytes each). -/
def defaultMaxPositions : Nat := 10000000

structure Opts where
  deal : Option Nat := none
  position : Option String := none
  limits : Limits := { maxPositions := some defaultMaxPositions }
  certificate : Option String := none
  moves : Bool := false
  json : Bool := false
  rest : List String := []
  /-- Options given, to reject repeats and options the command does not use. -/
  flags : List String := []

/-- Decimal digits only (`String.toNat?` would also accept `1_000`). -/
def parseNat (flag v : String) : Except String Nat :=
  if !v.isEmpty && v.all Char.isDigit then
    match v.toNat? with
    | some n => .ok n
    | none => .error s!"{flag} expects a natural number, got '{v}'"
  else .error s!"{flag} expects a natural number, got '{v}'"

def parseOpts : List String → Opts → Except String Opts
  | [], o => .ok { o with rest := o.rest.reverse }
  | a :: r, o =>
    if a.startsWith "--" && a ∈ o.flags then .error s!"option '{a}' given more than once"
    else parseOpt (a :: r) (if a.startsWith "--" then { o with flags := a :: o.flags } else o)
where
  parseOpt : List String → Opts → Except String Opts
  | [], o => .ok o
  | "--deal" :: v :: r, o => do parseOpts r { o with deal := some (← parseNat "--deal" v) }
  | "--position" :: v :: r, o => parseOpts r { o with position := some v }
  | "--max-positions" :: "unlimited" :: r, o => parseOpts r { o with limits := { o.limits with maxPositions := none } }
  | "--max-positions" :: v :: r, o => do
    parseOpts r { o with limits := { o.limits with maxPositions := some (← parseNat "--max-positions" v) } }
  | "--time-limit" :: v :: r, o => do
    parseOpts r { o with limits := { o.limits with timeLimitMs := some (1000 * (← parseNat "--time-limit" v)) } }
  | "--cancel-file" :: v :: r, o => parseOpts r { o with limits := { o.limits with cancelFile := some v } }
  | "--certificate" :: v :: r, o => parseOpts r { o with certificate := some v }
  | "--moves" :: r, o => parseOpts r { o with moves := true }
  | "--proposer-budget" :: v :: r, o => do
    parseOpts r { o with limits := { o.limits with proposerBudget := (← parseNat "--proposer-budget" v) } }
  | "--reference-only" :: r, o => parseOpts r { o with limits := { o.limits with proposerBudget := 0 } }
  | "--json" :: r, o => parseOpts r { o with json := true }
  | a :: r, o =>
    if a.startsWith "--" then .error s!"unknown or incomplete option '{a}'"
    else parseOpts r { o with rest := a :: o.rest }

/-- Reject options the command does not use. -/
def onlyFlags (cmd : String) (allowed : List String) (o : Opts) : Except String Opts :=
  match o.flags.find? (· ∉ allowed) with
  | some f => .error s!"option '{f}' does not apply to '{cmd}'"
  | none => .ok o

def positionFlags : List String := ["--deal", "--position"]
def solveFlags : List String := positionFlags ++ ["--max-positions", "--time-limit", "--cancel-file",
  "--certificate", "--moves", "--json", "--proposer-budget", "--reference-only"]

/-- Input errors: reported with exit status 2. -/
structure InputError where
  msg : String

abbrev CliM := ExceptT InputError IO

def inputError {α : Type} (msg : String) : CliM α := throw ⟨msg⟩

def liftE {α : Type} (ctx : String) : Except String α → CliM α
  | .ok a => pure a
  | .error e => inputError s!"{ctx}: {e}"

def readInput (path : String) : CliM String := do
  let r ← (if path = "-" then do (← IO.getStdin).readToEnd else IO.FS.readFile path).toBaseIO
  match r with
  | .ok t => pure t
  | .error e => inputError s!"cannot read {path}: {e}"

/-- The requested starting position, validated. -/
def requestedStart (o : Opts) : CliM { s : State // s.Valid } := do
  let s ← match o.deal, o.position with
    | some n, none =>
      unless 1 ≤ n ∧ n ≤ maxDeal do inputError s!"--deal must be between 1 and {maxDeal}"
      pure (msDeal n)
    | none, some p => liftE "position" (parsePosition (← readInput p))
    | none, none => inputError "give --deal N or --position FILE"
    | some _, some _ => inputError "give only one of --deal and --position"
  match checkValid s with
  | .ok ⟨s', hv, _⟩ => pure ⟨s', hv⟩
  | .error e => inputError e

def emit (o : Opts) (json : Json) (text : String) : IO Unit :=
  if o.json then IO.println json.compress else IO.print text

/-- Runtime failures: reported with exit status 1. -/
def failure (o : Opts) (msg : String) : IO UInt32 := do
  if o.json then IO.println (Json.mkObj [("result", toJson "error"), ("error", toJson msg)]).compress
  IO.eprintln s!"error: {msg}"
  return 1

/-- Write `text` to a new file via a temporary file and rename, so an interrupted write
never leaves a partial certificate at `path`. -/
def writeNew (path : String) (text : String) : IO Unit := do
  let tmp := s!"{path}.tmp-{← IO.Process.getPID}"
  IO.FS.writeFile tmp text
  IO.FS.rename tmp path

def cmdSolve (o : Opts) : CliM UInt32 := do
  unless o.rest.isEmpty do inputError s!"unexpected argument '{o.rest.head!}'"
  if let some p := o.certificate then
    if ← System.FilePath.pathExists p then
      inputError s!"certificate file {p} already exists; choose a new path"
  let ⟨start, hv⟩ ← requestedStart o
  let r ← solveBounded start hv o.limits
  match r with
  | .unknown reason n =>
    emit o (Json.mkObj [("result", toJson ("unknown")), ("reason", toJson (reason)), ("explored", toJson (n))])
      s!"unknown: {reason} after visiting {n} positions (this is not an impossibility proof)\n"
    return 3
  | .decided out engine n =>
    let cert := out.toCertificate
    let mut verified := false
    if let some path := o.certificate then
      -- write, then re-read the file and check it against the requested start
      let written ← (do writeNew path (writeCertificate cert); IO.FS.readFile path).toBaseIO
      match written with
      | .error e => return ← failure o s!"cannot write certificate {path}: {e}"
      | .ok text =>
        match verifyCertificate start text with
        | .ok _ => verified := true
        | .error e => return ← failure o s!"written certificate failed verification: {e}"
    match out with
    | .win ms _ =>
      let movesJ := if o.moves then [("moves", Json.arr (ms.map (Json.str ∘ showMove)).toArray)] else []
      emit o (Json.mkObj ([("result", toJson ("winnable")), ("moveCount", toJson (ms.length)),
          ("engine", toJson engine.name), ("explored", toJson (n)),
          ("certificate", toJson (match o.certificate with | some p => Json.str p | none => Json.null)),
          ("certificateVerified", if o.certificate.isSome then toJson verified else Json.null)] ++ movesJ))
        (s!"winnable: {ms.length} moves (found by the {engine.name} search, checked)\n" ++
          (if o.moves then String.join (ms.map (showMove · ++ "\n")) else ""))
    | .lose c _ =>
      emit o (Json.mkObj [("result", toJson ("unwinnable")), ("closedSetSize", toJson (c.size)),
          ("engine", toJson engine.name),
          ("certificate", toJson (match o.certificate with | some p => Json.str p | none => Json.null)),
          ("certificateVerified", if o.certificate.isSome then toJson verified else Json.null)])
        s!"unwinnable: every reachable position explored ({c.size} positions)\n"
    return 0

def cmdVerify (o : Opts) : CliM UInt32 := do
  let certPath ← match o.rest with
    | [p] => pure p
    | _ => inputError "verify expects exactly one CERTIFICATE argument"
  if certPath = "-" && o.position = some "-" then
    inputError "the position and the certificate cannot both come from standard input"
  let ⟨start, _⟩ ← requestedStart o
  let text ← readInput certPath
  match verifyCertificate start text with
  | .ok v =>
    let name := match v with | .winnable => "winnable" | .unwinnable => "unwinnable"
    emit o (Json.mkObj [("certificate", toJson ("accepted")), ("result", toJson (name))])
      s!"certificate accepted: the position is {name}\n"
    return 0
  | .error e =>
    emit o (Json.mkObj [("certificate", toJson ("rejected")), ("reason", toJson (e))]) s!"certificate rejected: {e}\n"
    return 4

def cmdDeal (o : Opts) : CliM UInt32 := do
  match o.rest with
  | [n] =>
    let g ← liftE "deal" (parseNat "deal" n)
    unless 1 ≤ g ∧ g ≤ maxDeal do inputError s!"deal must be between 1 and {maxDeal}"
    IO.print (showPosition (msDeal g))
    return 0
  | _ => inputError "deal expects one game number"

def cmdDeals (o : Opts) : CliM UInt32 := do
  match o.rest with
  | [a, b] =>
    let a ← liftE "deals" (parseNat "FROM" a)
    let b ← liftE "deals" (parseNat "TO" b)
    unless 1 ≤ a ∧ a ≤ b ∧ b ≤ maxDeal do inputError s!"deals expects 1 ≤ FROM ≤ TO ≤ {maxDeal}"
    let out ← IO.getStdout
    for g in [a:b + 1] do
      out.putStrLn s!"{g} {showCompact (msDeal g)}"
    return 0
  | _ => inputError "deals expects FROM and TO"

def main (args : List String) : IO UInt32 := do
  let run : CliM UInt32 := match args with
    | "solve" :: r => do cmdSolve (← liftE "arguments" (parseOpts r {} >>= onlyFlags "solve" solveFlags))
    | "verify" :: r => do
      cmdVerify (← liftE "arguments" (parseOpts r {} >>= onlyFlags "verify" (positionFlags ++ ["--json"])))
    | "deal" :: r => do cmdDeal (← liftE "arguments" (parseOpts r {} >>= onlyFlags "deal" []))
    | "deals" :: r => do cmdDeals (← liftE "arguments" (parseOpts r {} >>= onlyFlags "deals" []))
    | ["help"] | ["--help"] | ["-h"] => do IO.print usage; pure 0
    | _ => inputError "unknown command; try 'freecell help'"
  match ← run.run with
  | .ok code => return code
  | .error e =>
    IO.eprintln s!"error: {e.msg}"
    return 2

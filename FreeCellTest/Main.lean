import FreeCell
import FreeCellTest.Reference

/-!
Executable tests: `lake exe tests` from the repository root. These supplement the
Lean theorems with differential and negative evidence; they prove nothing general.
-/

open FreeCell Std

structure Tally where
  passed : Nat := 0
  failed : List String := []

abbrev TestM := StateT Tally IO

def check (name : String) (ok : Bool) (detail : String := "") : TestM Unit := do
  if ok then
    modify fun t => { t with passed := t.passed + 1 }
  else
    IO.println s!"FAIL {name} {detail}"
    modify fun t => { t with failed := name :: t.failed }

def section_ (name : String) : TestM Unit := IO.println s!"== {name}"

/-! ## Helpers -/

deriving instance Inhabited for Ref.State

def okEq {α : Type} [BEq α] : Except String α → α → Bool
  | .ok a, b => a == b
  | .error _, _ => false

def ofRefCard (c : Ref.Card) : Card := ⟨c.rank, c.suit⟩
def ofRef (s : Ref.State) : State :=
  ⟨s.cols.map (·.map ofRefCard), s.cells.map ofRefCard, s.home⟩

def isValid (s : State) : Bool := decide s.Valid

def card (t : String) : Card := (parseCard t).get!

def deal1 : State := msDeal 1

def lose11982 : HashSet State :=
  match solve (msDeal 11982) (msDeal_valid 11982) with
  | .lose c _ => c
  | .win .. => {}

def winPath (g : Nat) : List Move :=
  match solve (msDeal g) (msDeal_valid g) with
  | .win ms _ => ms
  | .lose .. => []

/-- Breadth-first exploration with the reference rules, up to `limit` positions. -/
def refExplore (start : Ref.State) (limit : Nat) : Array Ref.State := Id.run do
  let mut seen : HashSet Ref.State := HashSet.emptyWithCapacity 1024 |>.insert start
  let mut order : Array Ref.State := #[start]
  let mut i := 0
  while i < order.size && order.size < limit do
    for t in Ref.moves order[i]! do
      if !seen.contains t && order.size < limit then
        seen := seen.insert t
        order := order.push t
    i := i + 1
  return order

/-! ## Tests -/

def testValidity : TestM Unit := do
  section_ "validity"
  check "deal 1 valid" (isValid deal1)
  check "deal 11982 valid" (isValid (msDeal 11982))
  let c0 := deal1.cols.getD 0 []
  let dup := { deal1 with cols := deal1.cols.set 0 (c0.set 0 (card "TC")) }
  check "duplicate card rejected" (!isValid dup)
  let missing := { deal1 with cols := deal1.cols.set 0 c0.tail }
  check "missing card rejected" (!isValid missing)
  check "seven columns rejected" (!isValid { deal1 with cols := deal1.cols.take 7 })
  check "nine columns rejected" (!isValid { deal1 with cols := deal1.cols ++ [[]] })
  let extra := { deal1 with cols := deal1.cols.set 0 (card "AC" :: c0) }
  check "53 cards rejected" (!isValid extra)
  -- AC is in column 5 of deal 1; a clubs foundation of height 1 counts it twice
  check "foundation/card overlap rejected" (!isValid { deal1 with home := [1, 0, 0, 0] })
  check "three foundations rejected" (!isValid { deal1 with home := [0, 0, 0] })
  let allHome : State := ⟨List.replicate 8 [], [], [13, 13, 13, 13]⟩
  check "won position valid" (isValid allHome)
  check "foundation above king rejected" (!isValid { allHome with home := [14, 13, 13, 13] })
  check "foundation below 0 cards missing" (!isValid { allHome with home := [12, 13, 13, 13] })
  check "non-card rejected"
    (!isValid { allHome with home := [12, 13, 13, 13], cells := [⟨14, 0⟩] })
  -- free cells: KC moved out of the clubs foundation into a cell
  let kcCell : State := { allHome with home := [12, 13, 13, 13], cells := [card "KC"] }
  check "card in free cell valid" (isValid kcCell)
  let twoCells : State := { allHome with home := [12, 12, 13, 13], cells := [card "KD", card "KC"] }
  check "non-canonical cell order rejected" (!isValid twoCells)
  check "canonical cell order accepted" (isValid { twoCells with cells := [card "KC", card "KD"] })
  let threeCells : State :=
    ⟨List.replicate 7 [] ++ [[card "KS"]], [card "KC", card "KD", card "KH"], [12, 12, 12, 12]⟩
  check "three cells and a column card valid" (isValid threeCells)
  check "five cells rejected"
    (!isValid { allHome with home := [12, 12, 12, 11], cells := [card "KC", card "KD", card "QS", card "KH", card "KS"] })

def testDifferential : TestM Unit := do
  section_ "differential against the #11982 reference rules"
  let states := refExplore Ref.deal 200000
  check "reference reachable count 84767" (states.size == 84767) s!"{states.size}"
  let mut mismatches := 0
  let mut edgesRef := 0
  let mut edgesOurs := 0
  for s in states do
    let ours : HashSet State := HashSet.ofList (moves (ofRef s))
    let theirs : HashSet State := HashSet.ofList ((Ref.moves s).map ofRef)
    edgesRef := edgesRef + theirs.size
    edgesOurs := edgesOurs + ours.size
    unless ours.size == theirs.size && ours.toList.all theirs.contains do
      mismatches := mismatches + 1
  check "successor sets identical on all 84767 positions" (mismatches == 0) s!"{mismatches} differ"
  IO.println s!"   distinct edges: ours {edgesOurs}, reference {edgesRef} (independent Python baseline: 314366)"
  check "edge count matches independent baseline" (edgesOurs == 314366)
  check "closed set equals reference reachable set"
    (lose11982.size == states.size && states.all (fun s => lose11982.contains (ofRef s)))
  for g in [1, 617, 1941, 31465] do
    let refStart := Ref.State.mk (Ref.msDeal g) [] [0, 0, 0, 0]
    let part := refExplore refStart 20000
    let bad := part.filter fun s =>
      let ours : HashSet State := HashSet.ofList (moves (ofRef s))
      let theirs : HashSet State := HashSet.ofList ((Ref.moves s).map ofRef)
      !(ours.size == theirs.size && ours.toList.all theirs.contains)
    check s!"successor sets identical on 20000 positions of deal {g}" (bad.size == 0)
    check s!"reference and new deal {g} agree" (ofRef refStart == msDeal g)

def testClosedControls : TestM Unit := do
  section_ "unwinnable certificate controls (fresh, against new checker)"
  let start := msDeal 11982
  let c := lose11982
  check "closed set accepted" (checkClosed start c)
  check "start deleted rejected" (!checkClosed start (c.erase start))
  let others := c.toList.filter (· != start)
  check "first non-start position deleted rejected" (!checkClosed start (c.erase others.head!))
  check "last non-start position deleted rejected" (!checkClosed start (c.erase others.getLast!))
  let won : State := ⟨List.replicate 8 [], [], [13, 13, 13, 13]⟩
  check "won position inserted rejected" (!checkClosed start (c.insert won))
  check "empty set rejected" (!checkClosed start {})
  match initSearch start with
  | .inr σ =>
    for n in [0, 1, 1000, 20000] do
      match runSteps (msDeal_valid 11982) n σ with
      | .inr σ' => check s!"search truncated after {n} steps rejected" (!checkClosed start σ'.visited)
      | .inl _ => check s!"search truncated after {n} steps did not finish" false
  | .inl _ => check "initial search" false
  check "certificate for 11982 rejected for 11981" (!checkClosed (msDeal 11981) c)
  -- extra unreachable junk does not invalidate a closed set
  check "closed set plus unrelated closed position still closed"
    (checkClosed start (c.insert won |>.erase won))

def testWinControls : TestM Unit := do
  section_ "winning path controls"
  for g in [1, 617, 1941] do
    let ms := winPath g
    check s!"deal {g} solver path accepted" (checkWin (msDeal g) ms) s!"{ms.length} moves"
    check s!"deal {g} last move dropped rejected" (!checkWin (msDeal g) ms.dropLast)
    check s!"deal {g} first move dropped rejected" (!checkWin (msDeal g) ms.tail)
    check s!"deal {g} path rejected for another deal" (!checkWin (msDeal (g + 1)) ms)
    check s!"deal {g} empty path rejected" (!checkWin (msDeal g) [])
    let corrupted := ms.set (ms.length / 2) ⟨.col 0, .col 0⟩
    check s!"deal {g} corrupted move rejected" (!checkWin (msDeal g) corrupted)
  for g in [1, 617, 1941] do
    let text ← IO.FS.readFile s!"tests/fixtures/independent-win-{g}.cert"
    check s!"independent witness for deal {g} accepted" (okEq (verifyCertificate (msDeal g) text) .winnable)
    check s!"independent witness for deal {g} rejected for deal {g + 1}"
      (verifyCertificate (msDeal (g + 1)) text matches .error _)

def testDecision : TestM Unit := do
  section_ "decision procedure"
  check "11982 unwinnable" (!winnable (msDeal 11982) (msDeal_valid 11982))
  check "1 winnable" (winnable (msDeal 1) (msDeal_valid 1))
  let won : State := ⟨List.replicate 8 [], [], [13, 13, 13, 13]⟩
  match checkValid won with
  | .ok ⟨s, hv, _⟩ =>
    match solve s hv with
    | .win [] _ => check "won start: empty winning path" true
    | _ => check "won start: empty winning path" false
  | .error _ => check "won start valid" false
  -- one move from winning: KS in a cell
  let near : State := ⟨List.replicate 8 [], [card "KS"], [13, 13, 13, 12]⟩
  match checkValid near with
  | .ok ⟨s, hv, _⟩ =>
    match solve s hv with
    | .win ms _ => check "one move from won" (ms.length == 1 && ms.map showMove == ["f:KS h"])
    | _ => check "one move from won" false
  | .error _ => check "near-won valid" false

def testCodec : TestM Unit := do
  section_ "text formats"
  let mut bad := 0
  for g in [1:2001] do
    let s := msDeal g
    unless okEq (parsePosition (showPosition s)) s && okEq (parseCompact (showCompact s)) s do
      bad := bad + 1
  check "deal 1..2000 round trip" (bad == 0) s!"{bad}"
  let bad2 := lose11982.toList.filter fun s =>
    !(okEq (parsePosition (showPosition s)) s && okEq (parseCompact (showCompact s)) s)
  check "84767 reachable positions round trip" (bad2.isEmpty)
  let ms := winPath 1
  check "moves round trip" (ms.all fun m => okEq (parseMove (showMove m)) m)
  check "reject unknown card" (parsePosition ": ZZ\n:\n:\n:\n:\n:\n:\n:\n" matches .error _)
  check "reject seven columns" (parsePosition ": AS\n:\n:\n:\n:\n:\n:\n" matches .error _)
  check "reject five free cells" (parsePosition "Freecells: AS 2S 3S 4S 5S\n:\n:\n:\n:\n:\n:\n:\n:\n" matches .error _)
  check "reject duplicate foundation" (parsePosition "Foundations: S-A S-2\n:\n:\n:\n:\n:\n:\n:\n:\n" matches .error _)
  check "cells sorted on input"
    (match parsePosition "Freecells: KD KC\nFoundations: C-Q D-Q H-K S-K\n:\n:\n:\n:\n:\n:\n:\n:\n" with
      | .ok s => s.cells == [card "KC", card "KD"] && isValid s
      | .error _ => false)
  check "reject malformed move" (parseMove "c9 h" matches .error _)
  check "reject certificate with wrong rules"
    (parseCertificate "freecell-verified certificate v1\nrules: other\nstart: 0.0.0.0||\nwinnable: 0\n" matches .error _)
  check "reject certificate with wrong count"
    (verifyCertificate deal1 (writeCertificate ⟨deal1, .win (winPath 1)⟩ ++ "c1 h\n") matches .error _)

def main : IO UInt32 := do
  let ((), t) ← (do
    testValidity
    testDecision
    testDifferential
    testClosedControls
    testWinControls
    testCodec : TestM Unit).run {}
  IO.println s!"{t.passed} passed, {t.failed.length} failed"
  return if t.failed.isEmpty then 0 else 1

import FreeCell.Search
import FreeCell.Deal

/-!
# Text formats

Parsing is untrusted: a parser may return any value, and every result the
command line reports is established by a checker theorem about the value that
was actually parsed. The formats are deterministic so `parse ∘ print` is the
identity on the positions and moves this tool emits (tested, not proved).

**Position** (Freecell Solver style). Blank lines and `#` comments are ignored.

    Foundations: C-0 D-A H-2 S-0     (optional; heights 0 A 2 … 9 T J Q K)
    Freecells: QS 5H - -             (optional; at most four cards, `-` for empty)
    : KD QC JD                        (exactly eight column lines, bottom to top;
    :                                  a leading `:` is optional, `:` alone is empty)

Free cells are interchangeable; parsing sorts them into canonical order.

**Compact position**: one line, `h0.h1.h2.h3|cells|col1|…|col8`, cards space
separated, columns bottom to top. Used inside certificates; not canonicalised.

**Move**: `<src> <dst>` with src `c1`…`c8` or `f:<card>`, dst `h`, `c1`…`c8` or `f`.
-/

namespace FreeCell

def rankChars : List Char := "A23456789TJQK".toList
def suitChars : List Char := "CDHS".toList

def parseCard (tok : String) : Option Card :=
  match tok.toUpper.toList with
  | [r, s] => do
    let ri ← rankChars.idxOf? r
    let si ← suitChars.idxOf? s
    pure ⟨ri + 1, si⟩
  | ['1', '0', s] => do
    let si ← suitChars.idxOf? s
    pure ⟨10, si⟩
  | _ => none

def showCard (c : Card) : String := toString c

def words (s : String) : List String :=
  (s.split (fun c => c == ' ' || c == '\t')).toList.map (·.toString) |>.filter (· ≠ "")

def parseCards (ws : List String) : Except String (List Card) :=
  ws.mapM fun w => match parseCard w with
    | some c => .ok c
    | none => .error s!"invalid card '{w}'"

def parseHeight (t : String) : Option Nat :=
  if t = "0" then some 0 else
  match t.toUpper.toList with
  | [r] => (rankChars.idxOf? r).map (· + 1)
  | ['1', '0'] => some 10
  | _ => none

def heightChar (h : Nat) : String :=
  if h = 0 then "0" else (rankChars.getD (h - 1) '?').toString

/-- Sort free-cell cards into the canonical order used by the rules. -/
def sortCells (cs : List Card) : List Card := cs.foldr insertSorted []

def parseFoundations (ws : List String) : Except String (List Nat) := do
  let mut home := [0, 0, 0, 0]
  let mut seen : List Nat := []
  for w in ws do
    match w.toUpper.toList with
    | s :: '-' :: rest =>
      let some si := suitChars.idxOf? s | throw s!"invalid foundation '{w}'"
      if si ∈ seen then throw s!"foundation for suit {s} given twice"
      let some h := parseHeight (String.ofList rest) | throw s!"invalid foundation '{w}'"
      home := home.set si h
      seen := si :: seen
    | _ => throw s!"invalid foundation '{w}'"
  return home

/-- Parse a position. The result is not yet known to be valid; see `checkValid`. -/
def parsePosition (text : String) : Except String State := do
  let lines := (text.split (· == '\n')).toList.map (fun l => l.toString.trimAscii.toString)
    |>.filter fun l => l ≠ "" && !l.startsWith "#"
  let mut home : Option (List Nat) := none
  let mut cells : Option (List Card) := none
  let mut cols : Array (List Card) := #[]
  for l in lines do
    if l.startsWith "Foundations:" then
      if home.isSome then throw "duplicate Foundations line"
      home := some (← parseFoundations (words (l.drop "Foundations:".length).toString))
    else if l.startsWith "Freecells:" then
      if cells.isSome then throw "duplicate Freecells line"
      let ws := (words (l.drop "Freecells:".length).toString).filter (· ≠ "-")
      cells := some (← parseCards ws)
    else
      let body := if l.startsWith ":" then (l.drop 1).toString else l
      -- columns are written bottom to top; the model keeps the exposed card first
      cols := cols.push (← parseCards (words body)).reverse
  if cols.size ≠ 8 then throw s!"expected 8 columns, found {cols.size}"
  let cellCards := cells.getD []
  if cellCards.length > 4 then throw s!"at most 4 free cells, found {cellCards.length}"
  return { cols := cols.toList, cells := sortCells cellCards, home := home.getD [0, 0, 0, 0] }

def showPosition (s : State) : String :=
  let fnd := (List.range 4).map fun i => s!"{suitChars.getD i '?'}-{heightChar (s.home.getD i 0)}"
  let cells := s.cells.map showCard ++ List.replicate (4 - s.cells.length) "-"
  let cols := s.cols.map fun col => ":" ++ String.join (col.reverse.map (" " ++ showCard ·))
  String.intercalate "\n" ((s!"Foundations: {" ".intercalate fnd}") :: s!"Freecells: {" ".intercalate cells}" :: cols) ++ "\n"

/-- Explain why a parsed position is not valid. -/
def diagnose (s : State) : List String :=
  let cards := s.cards
  let bad := cards.filter (· ∉ deck)
  let dups := (deck.filter fun c => cards.count c > 1)
  let missing := deck.filter (· ∉ cards)
  (if s.cols.length ≠ 8 then ["wrong number of columns"] else []) ++
  (if s.home.any (· > 13) then ["foundation height above king"] else []) ++
  (bad.map fun c => s!"not a card: {repr c}") ++
  (dups.map fun c => s!"duplicate card {c} (counting foundations)") ++
  (missing.map fun c => s!"missing card {c}")

/-- Check validity, returning the proof so the solver can use it. -/
def checkValid (s : State) : Except String { s' : State // s'.Valid ∧ s' = s } :=
  if h : s.Valid then .ok ⟨s, h, rfl⟩
  else .error ("invalid position: " ++ ", ".intercalate (match diagnose s with
    | [] => ["cells not canonical"] | ds => ds))

/-! ## Compact positions -/

def showCompact (s : State) : String :=
  let cards (cs : List Card) := " ".intercalate (cs.map showCard)
  ".".intercalate (s.home.map toString) ++ "|" ++ cards s.cells ++ "|" ++
    "|".intercalate (s.cols.map fun col => cards col.reverse)

def parseCompact (line : String) : Except String State := do
  match (line.split (· == '|')).toList.map (·.toString) with
  | h :: c :: cs =>
    let home ← (h.split (· == '.')).toList.mapM fun t =>
      match t.toString.toNat? with
      | some n => .ok n
      | none => .error s!"invalid foundation height '{t}'"
    let cells ← parseCards (words c)
    let cols ← cs.mapM fun col => do return (← parseCards (words col)).reverse
    return { cols, cells, home }
  | _ => throw s!"malformed compact position"

/-! ## Moves -/

def parseColumn (t : String) : Option Nat :=
  match t.toList with
  | ['c', d] => if '1' ≤ d ∧ d ≤ '8' then some (d.toNat - '1'.toNat) else none
  | _ => none

def parseMove (line : String) : Except String Move :=
  match words line with
  | [a, b] => do
    let src ← if a.startsWith "f:" then
        match parseCard (a.drop 2).toString with
        | some c => pure (Src.cell c)
        | none => throw s!"invalid move source '{a}'"
      else match parseColumn a with
        | some i => pure (Src.col i)
        | none => throw s!"invalid move source '{a}'"
    let dst ← if b = "h" then pure Dst.home else if b = "f" then pure Dst.cell else
      match parseColumn b with
      | some j => pure (Dst.col j)
      | none => throw s!"invalid move destination '{b}'"
    return ⟨src, dst⟩
  | _ => throw s!"invalid move '{line}'"

def showMove (m : Move) : String :=
  let src := match m.src with
    | .col i => s!"c{i + 1}"
    | .cell c => s!"f:{c}"
  let dst := match m.dst with
    | .home => "h"
    | .col j => s!"c{j + 1}"
    | .cell => "f"
  s!"{src} {dst}"

end FreeCell

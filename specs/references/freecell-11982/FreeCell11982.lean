/-
  Microsoft FreeCell deal #11982 cannot be won.

  Trusted specification (read these; everything else is checked by Lean):
    * `msDeal`   — Microsoft's deal: the MSVC `rand()` LCG and the dealing loop.
    * `moves`    — the legal single-card moves of FreeCell with four free cells.
    * `Reachable`, `Won`.
  Multi-card "supermoves" are sequences of single-card moves, so they reach no
  position that single-card moves cannot.

  Method: `explore` (untrusted) gathers a set of positions; `checkCert` verifies
  that the set contains the deal, is closed under every legal move, and holds
  no won position. `cert_sound` proves such a set contains every reachable
  position. The check itself runs by `native_decide`, i.e. it trusts Lean's
  compiler (via a generated `_native` axiom).
-/
import Std.Data.HashSet
open Std

structure Card where
  rank : Nat   -- 1 = ace … 13 = king
  suit : Nat   -- 0 clubs, 1 diamonds, 2 hearts, 3 spades
deriving DecidableEq, Hashable, Repr, Inhabited

def Card.red (c : Card) : Bool := c.suit == 1 || c.suit == 2
def Card.code (c : Card) : Nat := (c.rank - 1) * 4 + c.suit

instance : ToString Card where
  toString c := s!"{"A23456789TJQK".toList.getD (c.rank - 1) '?'}{"CDHS".toList.getD c.suit '?'}"

structure State where
  cols  : List (List Card)  -- eight columns, head = top (exposed) card
  cells : List Card         -- free-cell contents, kept sorted: cells are interchangeable
  home  : List Nat          -- foundation heights for clubs, diamonds, hearts, spades
deriving DecidableEq, Hashable

/-! ## Microsoft's deal -/

/-- MSVC `rand()`: seed ← seed·214013 + 2531011 (mod 2³¹), output seed / 2¹⁶. -/
def lcg (seed : Nat) : Nat := (seed * 214013 + 2531011) % 2 ^ 31

/-- Deal order: deck starts AC AD AH AS 2C …; each step picks index `rand % remaining`,
    takes that card, and moves the last card into the hole. -/
def dealOrder (game : Nat) : List Card := Id.run do
  let mut deck : Array Card := (List.range 52).toArray.map fun i => ⟨i / 4 + 1, i % 4⟩
  let mut seed := game
  let mut out : Array Card := #[]
  for _ in [0:52] do
    seed := lcg seed
    let j := (seed / 2 ^ 16) % deck.size
    out := out.push deck[j]!
    deck := deck.set! j deck.back!   -- fill the hole with the last card
    deck := deck.pop
  return out.toList

/-- Cards go out left to right in rows of eight; the first eight end up at the bottom. -/
def msDeal (game : Nat) : List (List Card) :=
  (List.range 8).map fun j =>
    ((dealOrder game).zipIdx.filter (fun (_, k) => k % 8 == j)).map (·.1) |>.reverse

def deal : State := { cols := msDeal 11982, cells := [], home := [0, 0, 0, 0] }

/-! ## The rules -/

def canStack (c parent : Card) : Bool := parent.rank == c.rank + 1 && parent.red != c.red
def canHome (home : List Nat) (c : Card) : Bool := home.getD c.suit 0 + 1 == c.rank

def insertSorted (c : Card) : List Card → List Card
  | [] => [c]
  | d :: ds => if c.code ≤ d.code then c :: d :: ds else d :: insertSorted c ds

/-- Every position reachable in one legal single-card move. A card leaves the top of a column
    or a free cell, and goes to its foundation, onto an empty column, onto a column whose top
    card is one rank higher and of the opposite colour, or (from a column) into a free cell. -/
def moves (s : State) : List State :=
  let fromCols : List (Card × State × Option Nat) :=
    (List.range 8).filterMap fun i =>
      match s.cols.getD i [] with
      | [] => none
      | c :: rest => some (c, { s with cols := s.cols.set i rest }, some i)
  let fromCells : List (Card × State × Option Nat) :=
    s.cells.map fun c => (c, { s with cells := s.cells.erase c }, none)
  (fromCols ++ fromCells).flatMap fun (c, s', src) =>
    -- to its foundation
    (if canHome s.home c then [{ s' with home := s'.home.set c.suit c.rank }] else []) ++
    -- onto an empty column, or onto a card one higher of the opposite colour
    ((List.range 8).filterMap fun j =>
      if src == some j then none else
      match s'.cols.getD j [] with
      | [] => some { s' with cols := s'.cols.set j [c] }
      | p :: ps => if canStack c p then some { s' with cols := s'.cols.set j (c :: p :: ps) } else none) ++
    -- from a column into a free cell
    (if src.isSome && s'.cells.length < 4 then [{ s' with cells := insertSorted c s'.cells }] else [])

inductive Reachable : State → Prop
  | deal : Reachable deal
  | step {s t : State} : Reachable s → t ∈ moves s → Reachable t

def Won (s : State) : Prop := s.home = [13, 13, 13, 13]

/-! ## Certificate checking -/

def won (s : State) : Bool := s.home == [13, 13, 13, 13]

def checkCert (c : HashSet State) : Bool :=
  c.contains deal && c.toList.all fun s => !won s && (moves s).all c.contains

theorem cert_sound (c : HashSet State) (h : checkCert c = true) :
    ∀ s, Reachable s → c.contains s = true ∧ won s = false := by
  simp only [checkCert, Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true'] at h
  obtain ⟨hdeal, hall⟩ := h
  have key : ∀ s, c.contains s = true → won s = false ∧ ∀ t ∈ moves s, c.contains t = true := by
    intro s hs
    have := hall s (HashSet.mem_toList.mpr (HashSet.mem_iff_contains.mpr hs))
    exact this
  intro s hr
  induction hr with
  | deal => exact ⟨hdeal, (key _ hdeal).1⟩
  | step _ ht ih =>
    have hc := (key _ ih.1).2 _ ht
    exact ⟨hc, (key _ hc).1⟩

/-- Untrusted search that proposes the certificate (depth-first, with fuel). -/
def explore (fuel : Nat) : HashSet State :=
  go fuel [deal] (HashSet.emptyWithCapacity 200000 |>.insert deal)
where
  go : Nat → List State → HashSet State → HashSet State
  | 0, _, seen => seen
  | _, [], seen => seen
  | n + 1, s :: rest, seen =>
    let (todo, seen) := (moves s).foldl
      (fun (todo, seen) t => if seen.contains t then (todo, seen) else (t :: todo, seen.insert t))
      (rest, seen)
    go n todo seen

def certificate : HashSet State := explore 10000000

theorem certificate_ok : checkCert certificate = true := by native_decide

/-- **Theorem.** No position reachable from FreeCell deal #11982 is won. -/
theorem freecell_11982_unwinnable : ∀ s, Reachable s → ¬ Won s := by
  intro s hr hw
  have := (cert_sound certificate certificate_ok s hr).2
  simp [won, Won] at *
  simp [hw] at this

/-! Sanity output -/
#eval (msDeal 1).map fun col => col.reverse.map toString      -- game 1 must start JD 2D 9H JC
#eval (msDeal 11982).map fun col => col.reverse.map toString
#eval certificate.size
#print axioms freecell_11982_unwinnable

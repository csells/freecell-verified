import FreeCell.Card

/-!
# Positions

`cols` holds the eight tableau columns with the exposed card at the head.
`cells` holds the free-cell contents as a list sorted by `Card.code`: the four
cells are interchangeable, so a position records which cards occupy cells, not
which cell holds which card. `home` holds the four foundation heights, indexed
by suit; a height `h` means the suit's ace through rank `h` are home.

`Valid` is the finite-position invariant: exactly eight columns, at most four
cells in canonical order, four foundation heights, and the cards in columns,
cells and (implicitly) foundations form exactly one standard deck.
-/

namespace FreeCell

structure State where
  cols  : List (List Card)
  cells : List Card
  home  : List Nat
deriving DecidableEq, Hashable, Repr, Inhabited

/-- Cards implicitly on the foundations: ranks `1 … home[suit]` of each suit. -/
def homeCards (home : List Nat) : List Card :=
  (List.range 4).flatMap fun su => (List.range (home.getD su 0)).map fun r => ⟨r + 1, su⟩

namespace State

/-- Every card a position accounts for, physically present or implied by a foundation height. -/
def cards (s : State) : List Card := s.cols.flatten ++ s.cells ++ homeCards s.home

structure Valid (s : State) : Prop where
  cols_length : s.cols.length = 8
  cells_length : s.cells.length ≤ 4
  cells_sorted : s.cells.Pairwise (fun a b => a.code < b.code)
  home_length : s.home.length = 4
  home_le : ∀ h ∈ s.home, h ≤ 13
  cards_perm : s.cards.Perm deck

def Won (s : State) : Prop := s.home = [13, 13, 13, 13]

def won (s : State) : Bool := s.home == [13, 13, 13, 13]

theorem won_iff {s : State} : s.won = true ↔ s.Won := by simp [won, Won]

instance : DecidablePred Won := fun _ => decidable_of_iff _ won_iff

end State

/-- Insert a card into a free-cell list kept sorted by `Card.code`. -/
def insertSorted (c : Card) : List Card → List Card
  | [] => [c]
  | d :: ds => if c.code ≤ d.code then c :: d :: ds else d :: insertSorted c ds

end FreeCell

/-!
# Cards

A card is a rank and a suit. Ranks run 1 (ace) to 13 (king); suits are
0 clubs, 1 diamonds, 2 hearts, 3 spades (Microsoft's deck order). The type
itself does not bound these numbers; `deck` lists the 52 genuine cards and
`State.Valid` requires every card in a position to be one of them.
-/

namespace FreeCell

structure Card where
  rank : Nat
  suit : Nat
deriving DecidableEq, Hashable, Repr, Inhabited

namespace Card

def red (c : Card) : Bool := c.suit == 1 || c.suit == 2

/-- Position in Microsoft's fresh deck: AC AD AH AS 2C …; also the free-cell sort key. -/
def code (c : Card) : Nat := (c.rank - 1) * 4 + c.suit

def ofCode (i : Nat) : Card := ⟨i / 4 + 1, i % 4⟩

instance : ToString Card where
  toString c := s!"{"A23456789TJQK".toList.getD (c.rank - 1) '?'}{"CDHS".toList.getD c.suit '?'}"

/-- `c` may be placed on `parent` in the tableau: one rank lower, opposite colour. -/
def canStack (c parent : Card) : Bool := parent.rank == c.rank + 1 && parent.red != c.red

end Card

/-- The 52 cards, in Microsoft's fresh-deck order. -/
def deck : List Card := (List.range 52).map Card.ofCode

theorem mem_deck {c : Card} : c ∈ deck ↔ 1 ≤ c.rank ∧ c.rank ≤ 13 ∧ c.suit < 4 := by
  simp only [deck, List.mem_map, List.mem_range, Card.ofCode]
  constructor
  · rintro ⟨i, hi, rfl⟩; dsimp only; omega
  · obtain ⟨r, s⟩ := c
    rintro ⟨h1, h2, h3⟩
    refine ⟨(r - 1) * 4 + s, by dsimp only at *; omega, ?_⟩
    simp only [Card.mk.injEq] at *; omega

theorem deck_nodup : deck.Nodup := by decide

theorem code_inj {c d : Card} (hc : c ∈ deck) (hd : d ∈ deck) (h : c.code = d.code) : c = d := by
  rw [mem_deck] at hc hd
  cases c; cases d; simp only [Card.code] at *; simp only [Card.mk.injEq]; omega

end FreeCell

import FreeCell.Valid

/-!
# Finitely many valid positions

`allShapes` is an explicit (astronomically long, never evaluated) list containing
every valid position. Hence a duplicate-free collection of valid positions has
at most `stateBound` elements; the search's termination measure rests on this.
-/

namespace FreeCell

open List

variable {α : Type _}

/-- All lists of length at most `n` drawn from `xs`. -/
def listsUpTo (xs : List α) : Nat → List (List α)
  | 0 => [[]]
  | n + 1 => [] :: xs.flatMap fun a => (listsUpTo xs n).map (a :: ·)

theorem mem_listsUpTo {xs : List α} : ∀ {n : Nat} {l : List α},
    l.length ≤ n → (∀ a ∈ l, a ∈ xs) → l ∈ listsUpTo xs n
  | 0, [], _, _ => by simp [listsUpTo]
  | 0, _ :: _, h, _ => by simp at h
  | _ + 1, [], _, _ => by simp [listsUpTo]
  | n + 1, a :: l, h, hm => by
    simp only [listsUpTo, mem_cons, mem_flatMap, mem_map]
    refine Or.inr ⟨a, hm a (by simp), l, mem_listsUpTo (by simp at h; omega)
      (fun b hb => hm b (by simp [hb])), rfl⟩

/-- Every position whose components have the shapes of a valid one. -/
noncomputable def allShapes : List State :=
  (listsUpTo (listsUpTo deck 52) 8).flatMap fun cols =>
    (listsUpTo deck 4).flatMap fun cells =>
      (listsUpTo (range 14) 4).map fun home => ⟨cols, cells, home⟩

/-- An upper bound on the number of valid positions. -/
noncomputable def stateBound : Nat := allShapes.length

theorem State.Valid.mem_allShapes {s : State} (hv : s.Valid) : s ∈ allShapes := by
  have hlen : s.cards.length = 52 := by rw [hv.cards_perm.length_eq]; decide
  have hmem : ∀ c ∈ s.cards, c ∈ deck := fun c hc => hv.mem_deck hc
  simp only [allShapes, mem_flatMap, mem_map]
  refine ⟨s.cols, mem_listsUpTo (by simp [hv.cols_length]) ?_, s.cells,
    mem_listsUpTo hv.cells_length ?_, s.home, mem_listsUpTo (by simp [hv.home_length]) ?_, rfl⟩
  · intro col hcol
    have hsub : col <+ s.cards := by
      simp only [State.cards, append_assoc]
      exact (sublist_flatten_of_mem hcol).trans (sublist_append_left ..)
    exact mem_listsUpTo (by have := hsub.length_le; omega)
      (fun c hc => hmem c (hsub.subset hc))
  · intro c hc; exact hmem c (by simp [State.cards, hc])
  · intro h hh; have := hv.home_le h hh; simp; omega

/-- **Finiteness.** A duplicate-free list of valid positions has at most `stateBound` entries. -/
theorem length_le_stateBound {l : List State} (hnd : l.Nodup) (hv : ∀ s ∈ l, s.Valid) :
    l.length ≤ stateBound :=
  hnd.length_le_of_subset fun s hs => (hv s hs).mem_allShapes

end FreeCell

import FreeCell.Valid

/-!
# Microsoft numbered deals

`msDeal game` reproduces Microsoft FreeCell's deal for `game`: the MSVC `rand()`
linear congruential generator chooses a card from the remaining deck, and the
last remaining card fills the hole. Cards are dealt left to right in rows of
eight; later cards cover earlier ones.

`msDeal_valid` proves every game number yields a valid position. Agreement of the
layout with Microsoft's numbering is not a Lean theorem; it is checked against an
independent implementation for games 1–32000 (see `specs/evidence`).
-/

namespace FreeCell

open List

variable {α : Type _}

/-- MSVC `rand()` state update: seed ← seed·214013 + 2531011 (mod 2³¹); the output is seed / 2¹⁶. -/
def lcg (seed : Nat) : Nat := (seed * 214013 + 2531011) % 2 ^ 31

/-- Remove index `j`, moving the last element into the hole. -/
def swapRemove (d : List Card) (j : Nat) : Card × List Card :=
  match d.getLast? with
  | none => (default, [])
  | some last => (d.getD j default, (d.set j last).dropLast)

/-- The order in which cards are dealt, drawing `n` cards from deck `d`. -/
def dealOrderAux : Nat → Nat → List Card → List Card
  | 0, _, _ => []
  | n + 1, seed, d =>
    let seed' := lcg seed
    let (c, d') := swapRemove d ((seed' / 2 ^ 16) % d.length)
    c :: dealOrderAux n seed' d'

def dealOrder (game : Nat) : List Card := dealOrderAux 52 game deck

/-- Column `j` holds dealt cards `j, j+8, j+16, …`, the last of them exposed. -/
def msColumns (order : List Card) : List (List Card) :=
  (range 8).map fun j => ((order.zipIdx.filter fun p => p.2 % 8 == j).map (·.1)).reverse

def msDeal (game : Nat) : State := { cols := msColumns (dealOrder game), cells := [], home := [0, 0, 0, 0] }

/-! ## Validity -/

theorem cons_set_perm {l : List α} {j : Nat} {x y : α} (h : l[j]? = some y) :
    y :: l.set j x ~ x :: l := by
  induction l generalizing j with
  | nil => simp at h
  | cons a as ih =>
    cases j with
    | zero => simp at h; subst h; exact Perm.swap _ _ _
    | succ j =>
      simp only [getElem?_cons_succ] at h
      simp only [set_cons_succ]
      exact (Perm.swap _ _ _).trans (((ih h).cons a).trans (Perm.swap _ _ _))

theorem swapRemove_perm {d : List Card} {j : Nat} (hj : j < d.length) :
    (swapRemove d j).1 :: (swapRemove d j).2 ~ d ∧ (swapRemove d j).2.length + 1 = d.length := by
  obtain ⟨init, last, rfl⟩ : ∃ init last, d = init ++ [last] := by
    rcases eq_nil_or_concat d with rfl | ⟨init, last, rfl⟩
    · simp at hj
    · exact ⟨init, last, concat_eq_append ..⟩
  simp only [swapRemove, getLast?_append, getLast?_singleton, Option.some_or]
  rcases Nat.lt_or_ge j init.length with hlt | hge
  · rw [set_append_left _ _ hlt, dropLast_append_of_ne_nil (by simp), dropLast_singleton, append_nil]
    have hy : init[j]? = some (init.getD j default) := by simp [getD, hlt]
    have := cons_set_perm (x := last) hy
    refine ⟨?_, by simp⟩
    have hd : (init ++ [last]).getD j default = init.getD j default := by
      simp only [getD_eq_getElem?_getD, getElem?_append_left hlt]
    rw [hd]
    exact this.trans (perm_append_singleton _ _).symm
  · have hj' : j = init.length := by simp at hj; omega
    subst hj'
    rw [set_append_right _ _ (Nat.le_refl _), Nat.sub_self, set_cons_zero, dropLast_concat]
    refine ⟨?_, by simp⟩
    simp only [getD_eq_getElem?_getD, getElem?_append_right (Nat.le_refl _), Nat.sub_self,
      getElem?_cons_zero, Option.getD_some]
    exact (perm_append_singleton _ _).symm

theorem dealOrderAux_perm : ∀ (n seed : Nat) (d : List Card), d.length = n → dealOrderAux n seed d ~ d
  | 0, _, d, h => by simp [dealOrderAux, length_eq_zero_iff.mp h]
  | n + 1, seed, d, h => by
    simp only [dealOrderAux]
    have hj : (lcg seed / 2 ^ 16) % d.length < d.length := Nat.mod_lt _ (by omega)
    obtain ⟨hp, hl⟩ := swapRemove_perm hj
    exact ((dealOrderAux_perm n _ _ (by omega)).cons _).trans hp

theorem dealOrder_perm (game : Nat) : dealOrder game ~ deck :=
  dealOrderAux_perm 52 game deck (by decide)

theorem flatMap_perm_of_perm {is : List Nat} {f g : Nat → List α} (h : ∀ j ∈ is, f j ~ g j) :
    is.flatMap f ~ is.flatMap g := by
  induction is with
  | nil => simp
  | cons j js ih =>
    simp only [flatMap_cons]
    exact (h j (by simp)).append (ih fun k hk => h k (by simp [hk]))

/-- Distributing a list into columns by index modulo 8 is a permutation. -/
theorem flatMap_filter_mod_perm : ∀ (L : List (α × Nat)),
    (range 8).flatMap (fun j => (L.filter fun p => p.2 % 8 == j).map (·.1)) ~ L.map (·.1)
  | [] => by simp
  | x :: L => by
    have ih := flatMap_filter_mod_perm L
    have : (range 8).flatMap (fun j => ((x :: L).filter fun p => p.2 % 8 == j).map (·.1)) ~
        x.1 :: (range 8).flatMap (fun j => (L.filter fun p => p.2 % 8 == j).map (·.1)) := by
      apply flatMap_perm_cons nodup_range (k := x.2 % 8) (mem_range.mpr (Nat.mod_lt _ (by decide)))
      · simp
      · intro j hj; simp [Ne.symm hj]
    exact this.trans (ih.cons _)

theorem map_fst_zipIdx (l : List α) (i : Nat) : (l.zipIdx i).map (·.1) = l := by
  induction l generalizing i with
  | nil => rfl
  | cons a as ih => simp [ih]

theorem msColumns_perm (order : List Card) : (msColumns order).flatten ~ order := by
  simp only [msColumns, ← flatMap_def]
  have h1 := flatMap_perm_of_perm (is := range 8)
    (f := fun j => ((order.zipIdx.filter fun p => p.2 % 8 == j).map (·.1)).reverse)
    (g := fun j => (order.zipIdx.filter fun p => p.2 % 8 == j).map (·.1)) (fun _ _ => reverse_perm _)
  have h2 := flatMap_filter_mod_perm order.zipIdx
  rw [map_fst_zipIdx] at h2
  exact h1.trans h2

/-- **Every Microsoft deal is a valid position.** -/
theorem msDeal_valid (game : Nat) : (msDeal game).Valid where
  cols_length := by simp [msDeal, msColumns]
  cells_length := by simp [msDeal]
  cells_sorted := by simp [msDeal]
  home_length := rfl
  home_le := by simp [msDeal]
  cards_perm := by
    have : homeCards [0, 0, 0, 0] = [] := by decide
    simp only [State.cards, msDeal, this, append_nil]
    exact (msColumns_perm _).trans (dealOrder_perm game)

end FreeCell

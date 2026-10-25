import FreeCell.Rules

/-!
# Moves preserve validity

`Legal.valid`: a legal move from a valid position yields a valid position. The
core fact is card conservation: lifting a card removes exactly that card from
the position's card list and putting it adds exactly that card back.
-/

namespace FreeCell

open List

variable {α : Type _}

theorem lt_of_getElem?_eq_some {l : List α} {i : Nat} {x : α} (h : l[i]? = some x) : i < l.length :=
  (List.getElem?_eq_some_iff.mp h).1

theorem flatten_perm_set_nil {l : List (List α)} {i : Nat} {x : List α} (h : l[i]? = some x) :
    l.flatten ~ x ++ (l.set i []).flatten := by
  induction l generalizing i with
  | nil => simp at h
  | cons y ys ih =>
    cases i with
    | zero => simp at h; subst h; simp
    | succ i =>
      simp only [getElem?_cons_succ] at h
      simp only [flatten_cons, set_cons_succ]
      exact ((ih h).append_left y).trans
        (by rw [← append_assoc, ← append_assoc]; exact perm_append_comm.append_right _)

theorem flatten_set_perm {l : List (List α)} {i : Nat} {x y : List α} (h : l[i]? = some x) :
    (l.set i y).flatten ++ x ~ l.flatten ++ y := by
  have h1 := flatten_perm_set_nil h
  have h2 : (l.set i y)[i]? = some y := by simp [lt_of_getElem?_eq_some h]
  have h3 := flatten_perm_set_nil h2
  rw [set_set] at h3
  calc (l.set i y).flatten ++ x ~ (y ++ (l.set i []).flatten) ++ x := h3.append_right x
    _ ~ ((l.set i []).flatten ++ x) ++ y := by
        rw [append_assoc]; exact perm_append_comm
    _ ~ (x ++ (l.set i []).flatten) ++ y := perm_append_comm.append_right y
    _ ~ l.flatten ++ y := h1.symm.append_right y

theorem perm_insertSorted (c : Card) (l : List Card) : insertSorted c l ~ c :: l := by
  induction l with
  | nil => simp [insertSorted]
  | cons d ds ih =>
    simp only [insertSorted]
    split
    · exact Perm.refl _
    · exact (ih.cons d).trans (Perm.swap c d ds)

theorem pairwise_insertSorted {c : Card} {l : List Card}
    (hl : l.Pairwise (fun a b => a.code < b.code)) (hc : ∀ d ∈ l, c.code ≠ d.code) :
    (insertSorted c l).Pairwise (fun a b => a.code < b.code) := by
  induction l with
  | nil => simp [insertSorted]
  | cons d ds ih =>
    simp only [insertSorted]
    rw [pairwise_cons] at hl
    split
    · rename_i hle
      have hne := hc d (by simp)
      refine pairwise_cons.mpr ⟨?_, pairwise_cons.mpr hl⟩
      intro e he
      simp only [mem_cons] at he
      rcases he with rfl | he
      · omega
      · have := hl.1 e he; omega
    · rename_i hgt
      refine pairwise_cons.mpr ⟨?_, ih hl.2 (fun e he => hc e (by simp [he]))⟩
      intro e he
      have he' := (perm_insertSorted c ds).mem_iff.mp he
      simp only [mem_cons] at he'
      rcases he' with rfl | he'
      · omega
      · exact hl.1 e he'

/-- Generic: changing one index's contribution to a flatMap by consing one element. -/
theorem flatMap_perm_cons {is : List Nat} (hnd : is.Nodup) {k : Nat} (hk : k ∈ is)
    {f g : Nat → List α} {a : α} (hk' : g k ~ a :: f k) (hother : ∀ j, j ≠ k → g j = f j) :
    is.flatMap g ~ a :: is.flatMap f := by
  induction is with
  | nil => simp at hk
  | cons j js ih =>
    rw [nodup_cons] at hnd
    simp only [flatMap_cons]
    by_cases hjk : j = k
    · subst hjk
      have : js.flatMap g = js.flatMap f := by
        simp only [flatMap_def]; congr 1; apply map_congr_left
        intro x hx; exact hother x (fun h => hnd.1 (h ▸ hx))
      rw [this]; exact hk'.append_right _
    · have hk2 : k ∈ js := by simp only [mem_cons] at hk; rcases hk with h | h; exact absurd h.symm hjk; exact h
      rw [hother j hjk]
      exact ((ih hnd.2 hk2).append_left (f j)).trans perm_middle

theorem homeCards_set {home : List Nat} {su h : Nat} (hsu : su < 4) (hh : home[su]? = some h) :
    homeCards (home.set su (h + 1)) ~ ⟨h + 1, su⟩ :: homeCards home := by
  unfold homeCards
  apply flatMap_perm_cons nodup_range (mem_range.mpr hsu)
  · have hlt : su < home.length := lt_of_getElem?_eq_some hh
    have hget : home.getD su 0 = h := by simp [getD, hh]
    simp only [getD_eq_getElem?_getD, getElem?_set_self hlt, Option.getD_some, range_succ, map_append,
      map_cons, map_nil]
    rw [← getD_eq_getElem?_getD, hget]
    exact perm_append_comm
  · intro j hj
    simp only [getD_eq_getElem?_getD, getElem?_set_ne (Ne.symm hj)]

theorem Pick.cards_perm {s : State} {src : Src} {c : Card} {u : State} (h : Pick s src c u) :
    s.cards ~ c :: u.cards := by
  cases h with
  | col hi hcol =>
    rename_i i rest
    have hlt := lt_of_getElem?_eq_some hcol
    have h1 := flatten_perm_set_nil hcol
    have h2 : (s.cols.set i rest)[i]? = some rest := by simp [hlt]
    have h3 := flatten_perm_set_nil h2
    rw [set_set] at h3
    have h4 : s.cols.flatten ~ c :: (s.cols.set i rest).flatten := h1.trans (h3.symm.cons c)
    simp only [State.cards]
    simpa [append_assoc] using h4.append_right (s.cells ++ homeCards s.home)
  | cell hc =>
    simp only [State.cards]
    have := perm_cons_erase hc
    calc s.cols.flatten ++ s.cells ++ homeCards s.home
        ~ s.cols.flatten ++ (c :: s.cells.erase c) ++ homeCards s.home :=
          (this.append_left _).append_right _
      _ ~ c :: (s.cols.flatten ++ s.cells.erase c ++ homeCards s.home) := by
          simp only [append_assoc, cons_append]; exact perm_middle

theorem Put.cards_perm {u : State} {src : Src} {c : Card} {dst : Dst} {t : State}
    (h : Put u src c dst t) (hc : c ∈ deck) : t.cards ~ c :: u.cards := by
  cases h with
  | home hh hr =>
    rename_i hgt
    simp only [State.cards]
    have hsu : c.suit < 4 := (mem_deck.mp hc).2.2
    have := homeCards_set hsu hh
    have hcard : (⟨hgt + 1, c.suit⟩ : Card) = c := by cases c; simp_all
    rw [← hr]
    rw [hcard] at this
    calc u.cols.flatten ++ u.cells ++ homeCards (u.home.set c.suit (hgt + 1))
        ~ u.cols.flatten ++ u.cells ++ (c :: homeCards u.home) := this.append_left _
      _ ~ c :: (u.cols.flatten ++ u.cells ++ homeCards u.home) := perm_middle
  | empty hj _ he =>
    simp only [State.cards]
    have := flatten_set_perm (y := [c]) he
    simp only [append_nil] at this
    simpa [append_assoc] using (this.trans (perm_append_singleton _ _)).append_right _
  | stack hj hs hp hr hcol =>
    rename_i p ps j
    simp only [State.cards]
    have := flatten_set_perm (y := c :: p :: ps) hp
    have h2 : (u.cols.set j (c :: p :: ps)).flatten ~ c :: u.cols.flatten := by
      have := this.trans (perm_middle (l₁ := u.cols.flatten))
      rw [← cons_append] at this
      exact (perm_append_right_iff _).mp (this.trans (by simp))
    simpa [append_assoc] using h2.append_right _
  | cell hl =>
    simp only [State.cards]
    calc u.cols.flatten ++ insertSorted c u.cells ++ homeCards u.home
        ~ u.cols.flatten ++ (c :: u.cells) ++ homeCards u.home :=
          ((perm_insertSorted c u.cells).append_left _).append_right _
      _ ~ c :: (u.cols.flatten ++ u.cells ++ homeCards u.home) := by
          simp only [append_assoc, cons_append]; exact perm_middle

theorem Pick.mem_cards {s : State} {src : Src} {c : Card} {u : State} (h : Pick s src c u) :
    c ∈ s.cards := h.cards_perm.mem_iff.mpr (mem_cons_self ..)

theorem Legal.cards_perm {s : State} {m : Move} {t : State} (hv : s.Valid) (h : Legal s m t) :
    t.cards ~ s.cards := by
  obtain ⟨c, u, hp, hq⟩ := h
  have hc : c ∈ deck := hv.cards_perm.mem_iff.mp hp.mem_cards
  exact (hq.cards_perm hc).trans hp.cards_perm.symm

theorem State.Valid.mem_deck {s : State} (hv : s.Valid) {c : Card} (h : c ∈ s.cards) : c ∈ deck :=
  hv.cards_perm.mem_iff.mp h

theorem State.Valid.nodup {s : State} (hv : s.Valid) : s.cards.Nodup :=
  hv.cards_perm.nodup_iff.mpr deck_nodup

/-- **Validity preservation.** -/
theorem Legal.valid {s : State} {m : Move} {t : State} (hv : s.Valid) (h : Legal s m t) :
    t.Valid := by
  have hperm : t.cards ~ deck := (h.cards_perm hv).trans hv.cards_perm
  obtain ⟨src, dst⟩ := m
  obtain ⟨c, u, hp, hq⟩ := h
  have hc : c ∈ deck := hv.cards_perm.mem_iff.mp hp.mem_cards
  -- facts about the intermediate position `u`
  have hu_cols : u.cols.length = 8 := by
    cases hp <;> simp [hv.cols_length]
  have hu_cells_len : u.cells.length ≤ 4 := by
    cases hp with
    | col => exact hv.cells_length
    | cell hc' => have := length_erase_le (l := s.cells) (a := c); simp only; have := hv.cells_length; omega
  have hu_sorted : u.cells.Pairwise (fun a b => a.code < b.code) := by
    cases hp with
    | col => exact hv.cells_sorted
    | cell => exact hv.cells_sorted.sublist (erase_sublist)
  have hu_home : u.home = s.home := by cases hp <;> rfl
  have tnd : t.cards.Nodup := hperm.nodup_iff.mpr deck_nodup
  have tmem : ∀ d ∈ t.cards, d ∈ deck := fun d hd => hperm.mem_iff.mp hd
  cases hq with
  | home hh hr =>
    refine ⟨hu_cols, hu_cells_len, hu_sorted, ?_, ?_, hperm⟩
    · simp [hu_home, hv.home_length]
    · intro x hx
      have := mem_or_eq_of_mem_set hx
      rcases this with hx | rfl
      · exact hv.home_le x (hu_home ▸ hx)
      · exact (mem_deck.mp hc).2.1
  | empty => exact ⟨by simp [hu_cols], hu_cells_len, hu_sorted, by simp [hu_home, hv.home_length],
      by simpa [hu_home] using hv.home_le, hperm⟩
  | stack => exact ⟨by simp [hu_cols], hu_cells_len, hu_sorted, by simp [hu_home, hv.home_length],
      by simpa [hu_home] using hv.home_le, hperm⟩
  | cell hl =>
    refine ⟨hu_cols, ?_, ?_, by simp [hu_home, hv.home_length], by simpa [hu_home] using hv.home_le,
      hperm⟩
    · simp only [(perm_insertSorted c u.cells).length_eq, length_cons]; omega
    · apply pairwise_insertSorted hu_sorted
      intro d hd hcode
      -- `c` and `d` are distinct cards of `t`, both genuine, so their codes differ
      have hsub : (c :: u.cells).Nodup := by
        have hsl : insertSorted c u.cells <+ State.cards { u with cells := insertSorted c u.cells } := by
          simp only [State.cards]
          exact (sublist_append_right ..).trans (sublist_append_left ..)
        have : (insertSorted c u.cells).Nodup := tnd.sublist hsl
        exact (perm_insertSorted c u.cells).nodup_iff.mp this
      have hcd : c ≠ d := fun e => (nodup_cons.mp hsub).1 (e ▸ hd)
      have hdmem : d ∈ deck := tmem d (by
        simp only [State.cards, mem_append]
        exact Or.inl (Or.inr ((perm_insertSorted c u.cells).mem_iff.mpr (mem_cons_of_mem _ hd))))
      exact hcd (code_inj hc hdmem hcode)

theorem Step.valid {s t : State} (hv : s.Valid) (h : Step s t) : t.Valid :=
  let ⟨_, hm⟩ := h; hm.valid hv

end FreeCell

namespace FreeCell

instance State.decValid (s : State) : Decidable s.Valid :=
  decidable_of_iff (s.cols.length = 8 ∧ s.cells.length ≤ 4 ∧
      s.cells.Pairwise (fun a b => a.code < b.code) ∧ s.home.length = 4 ∧
      (∀ h ∈ s.home, h ≤ 13) ∧ s.cards.Perm deck)
    ⟨fun ⟨a, b, c, d, e, f⟩ => ⟨a, b, c, d, e, f⟩, fun ⟨a, b, c, d, e, f⟩ => ⟨a, b, c, d, e, f⟩⟩

end FreeCell

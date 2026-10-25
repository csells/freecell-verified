import FreeCell.Reach

/-!
# Supermoves

A supermove carries a properly built run of `k` cards from the top of one column
to another column in a single step. Players and solvers treat it as one move,
but it is only a shorthand: the standard capacity limit
`k ≤ (free cells + 1) · 2 ^ (empty columns)` is exactly what lets the run be
moved one card at a time using the free cells and the empty columns as
scratch space. Empty columns are counted among the columns other than the
source and the destination, so moving to an empty column halves the capacity.

`Supermove.reachable` proves the decomposition, and `superReachable_iff` that
adding supermoves to the single-card rules changes no reachability (and hence
no winnability) question.
-/

namespace FreeCell

open List

/-- `c` may be placed on `p`: `p` is one rank higher and of the opposite colour (as in `Put.stack`). -/
def Fits (c p : Card) : Prop := p.rank = c.rank + 1 ∧ p.red ≠ c.red

/-- A properly built run, head first: each card fits on the card below it. -/
inductive Built : List Card → Prop
  | nil : Built []
  | single (c : Card) : Built [c]
  | cons {c p : Card} {rest : List Card} : Fits c p → Built (p :: rest) → Built (c :: p :: rest)

/-- The bottom card of `run` fits on the exposed card of `dest` (vacuous if either is empty). -/
def Lands (run dest : List Card) : Prop := ∀ c ∈ run.getLast?, ∀ p ∈ dest.head?, Fits c p

/-- The columns other than `i` and `j` that are empty in `s`. -/
def emptyCols (s : State) (i j : Nat) : List Nat :=
  (List.range 8).filter fun k => decide (k ≠ i ∧ k ≠ j ∧ s.cols[k]? = some [])

/-- How many cards a supermove from column `i` to column `j` may carry. -/
def capacity (s : State) (i j : Nat) : Nat := (4 - s.cells.length + 1) * 2 ^ (emptyCols s i j).length

/-- `Supermove s t`: the top cards `run` of column `i` form a built run of at most
`capacity s i j` cards and move as a unit onto column `j`, giving `t`. -/
def Supermove (s t : State) : Prop :=
  ∃ (i j : Nat) (run rest dest : List Card),
    i < 8 ∧ j < 8 ∧ i ≠ j ∧ run ≠ [] ∧
    s.cols[i]? = some (run ++ rest) ∧ s.cols[j]? = some dest ∧
    Built run ∧ Lands run dest ∧ run.length ≤ capacity s i j ∧
    t = { s with cols := (s.cols.set i rest).set j (run ++ dest) }

/-- A single-card move or a supermove. -/
def SuperStep (s t : State) : Prop := Step s t ∨ Supermove s t

inductive SuperReachable (start : State) : State → Prop
  | refl : SuperReachable start start
  | tail {s t : State} : SuperReachable start s → SuperStep s t → SuperReachable start t

/-! ## Helper facts -/

theorem Reachable.trans {a b c : State} (hab : Reachable a b) (hbc : Reachable b c) : Reachable a c := by
  induction hbc with
  | refl => exact hab
  | tail _ hst ih => exact .tail ih hst

theorem Reachable.single {s t : State} (h : Step s t) : Reachable s t := .tail .refl h

theorem Built.of_append_left : ∀ {a b : List Card}, Built (a ++ b) → Built a
  | [], _, _ => .nil
  | [c], _, _ => .single c
  | c :: d :: a, b, h => by
    cases h with
    | cons hf h' => exact .cons hf (Built.of_append_left (b := b) h')

theorem Built.of_append_right : ∀ {a b : List Card}, Built (a ++ b) → Built b
  | [], _, h => h
  | [_], [], _ => .nil
  | [_], _ :: _, h => by cases h with | cons _ h' => exact h'
  | _ :: d :: a, b, h => by
    cases h with
    | cons _ h' => exact Built.of_append_right (a := d :: a) h'

theorem Built.link : ∀ {a : List Card} {b : Card} {bs : List Card}, Built (a ++ b :: bs) →
    ∀ c ∈ a.getLast?, Fits c b
  | [], _, _, _, c, hc => by simp at hc
  | [x], _, _, h, c, hc => by
    simp at hc; subst hc; cases h with | cons hf _ => exact hf
  | x :: y :: a, b, bs, h, c, hc => by
    cases h with
    | cons _ h' =>
      simp only [getLast?_cons_cons] at hc
      exact Built.link (a := y :: a) h' c hc

theorem erase_insertSorted {c : Card} : ∀ {l : List Card}, c ∉ l → (insertSorted c l).erase c = l
  | [], _ => by simp [insertSorted]
  | d :: ds, h => by
    simp only [insertSorted]
    split
    · simp
    · have hcd : d ≠ c := fun e => h (e ▸ mem_cons_self ..)
      rw [erase_cons_tail (by simpa using hcd), erase_insertSorted (fun h' => h (mem_cons_of_mem _ h'))]

theorem length_insertSorted (c : Card) (l : List Card) : (insertSorted c l).length = l.length + 1 :=
  (perm_insertSorted c l).length_eq

theorem mem_insertSorted_self (c : Card) (l : List Card) : c ∈ insertSorted c l :=
  (perm_insertSorted c l).mem_iff.mpr (mem_cons_self ..)

/-- A card in a column of a valid position is not in a free cell. -/
theorem not_mem_cells {cols : List (List Card)} {cells : List Card} {home : List Nat}
    (hv : (State.mk cols cells home).Valid) {i : Nat} {c : Card} {rest : List Card}
    (h : cols[i]? = some (c :: rest)) : c ∉ cells := by
  intro hc
  have hnd := hv.nodup
  simp only [State.cards, append_assoc] at hnd
  have hnd' := (nodup_append.mp hnd).2.2
  have hcol : c ∈ cols.flatten := mem_flatten.mpr ⟨c :: rest, mem_of_getElem? h, mem_cons_self ..⟩
  exact hnd' c hcol c (mem_append_left _ hc) rfl

/-! ## Moving a run through the free cells -/

theorem viaCells : ∀ (run : List Card) {cols : List (List Card)} {cells : List Card} {home : List Nat}
    {i j : Nat} {rest dest : List Card},
    (State.mk cols cells home).Valid → i < 8 → j < 8 → i ≠ j → run ≠ [] → Built run →
    Lands run dest → cols[i]? = some (run ++ rest) → cols[j]? = some dest →
    run.length ≤ 4 - cells.length + 1 →
    Reachable ⟨cols, cells, home⟩ ⟨(cols.set i rest).set j (run ++ dest), cells, home⟩
  | [], _, _, _, _, _, _, _, _, _, _, _, hne, _, _, _, _, _ => absurd rfl hne
  | [c], cols, cells, home, i, j, rest, dest, hv, hi, hj, hij, _, _, hl, hci, hcj, _ => by
    have hsrc : Src.col i ≠ Src.col j := fun e => hij (Src.col.inj e)
    have hpick : Pick ⟨cols, cells, home⟩ (.col i) c ⟨cols.set i rest, cells, home⟩ :=
      Pick.col hi (by simpa using hci)
    have hcj' : (cols.set i rest)[j]? = some dest := by rw [getElem?_set_ne hij]; exact hcj
    apply Reachable.single
    cases dest with
    | nil => exact ⟨⟨.col i, .col j⟩, c, _, hpick, Put.empty hj hsrc hcj'⟩
    | cons p ps =>
      have hf : Fits c p := hl c (by simp) p (by simp)
      exact ⟨⟨.col i, .col j⟩, c, _, hpick, Put.stack hj hsrc hcj' hf.1 hf.2⟩
  | c :: d :: r, cols, cells, home, i, j, rest, dest, hv, hi, hj, hij, _, hb, hl, hci, hcj, hlen => by
    have hsrc : Src.col i ≠ Src.col j := fun e => hij (Src.col.inj e)
    have hilt : i < cols.length := lt_of_getElem?_eq_some hci
    have hcells : cells.length < 4 := by simp at hlen; omega
    have hcnot : c ∉ cells := not_mem_cells hv (rest := (d :: r) ++ rest) (by simpa using hci)
    cases hb with
    | cons hf hb' =>
    -- 1. the top card goes to a free cell
    let cols1 := cols.set i ((d :: r) ++ rest)
    have h1 : Step ⟨cols, cells, home⟩ ⟨cols1, insertSorted c cells, home⟩ :=
      ⟨⟨.col i, .cell⟩, c, _, Pick.col hi (by simpa using hci), Put.cell hcells⟩
    have hv1 := h1.valid hv
    -- 2. the rest of the run moves, with one free cell fewer
    have h2 := viaCells (d :: r) (rest := rest) (dest := dest) hv1 hi hj hij (by simp) hb'
      (fun x hx p hp => hl x (by simpa using hx) p hp) (by simp [cols1, hilt])
      (by simp only [cols1]; rw [getElem?_set_ne hij]; exact hcj)
      (by simp [length_insertSorted] at hlen ⊢; omega)
    let cols2 := (cols1.set i rest).set j ((d :: r) ++ dest)
    have hjlt : j < cols.length := lt_of_getElem?_eq_some hcj
    -- 3. the top card comes back from its cell onto the run
    have h3 : Step ⟨cols2, insertSorted c cells, home⟩
        ⟨cols2.set j (c :: d :: (r ++ dest)), (insertSorted c cells).erase c, home⟩ :=
      ⟨⟨.cell c, .col j⟩, c, _, Pick.cell (mem_insertSorted_self c cells),
        Put.stack hj (by simp) (by simp [cols2, cols1, hjlt]) hf.1 hf.2⟩
    have heq : cols2.set j (c :: d :: (r ++ dest)) = (cols.set i rest).set j (c :: d :: r ++ dest) := by
      simp [cols2, cols1]
    rw [erase_insertSorted hcnot, heq] at h3
    exact ((Reachable.single h1).trans h2).trans (Reachable.single h3)

/-! ## Moving a run through empty columns -/

/-- The supermove decomposition, with `es` a list of distinct empty scratch columns. -/
theorem viaCols : ∀ (es : List Nat) {cols : List (List Card)} {cells : List Card} {home : List Nat}
    {i j : Nat} {run rest dest : List Card},
    (State.mk cols cells home).Valid → i < 8 → j < 8 → i ≠ j → run ≠ [] → Built run →
    Lands run dest → cols[i]? = some (run ++ rest) → cols[j]? = some dest →
    es.Nodup → (∀ k ∈ es, k < 8 ∧ k ≠ i ∧ k ≠ j ∧ cols[k]? = some []) →
    run.length ≤ (4 - cells.length + 1) * 2 ^ es.length →
    Reachable ⟨cols, cells, home⟩ ⟨(cols.set i rest).set j (run ++ dest), cells, home⟩
  | [], _, _, _, _, _, run, _, _, hv, hi, hj, hij, hne, hb, hl, hci, hcj, _, _, hlen =>
    viaCells run hv hi hj hij hne hb hl hci hcj (by simpa using hlen)
  | k :: es, cols, cells, home, i, j, run, rest, dest, hv, hi, hj, hij, hne, hb, hl, hci, hcj, hnd,
      hes, hlen => by
    rw [nodup_cons] at hnd
    have hes' : ∀ k' ∈ es, k' < 8 ∧ k' ≠ i ∧ k' ≠ j ∧ cols[k']? = some [] :=
      fun k' h => hes k' (mem_cons_of_mem _ h)
    obtain ⟨hk, hki, hkj, hck⟩ := hes k (mem_cons_self ..)
    have hkes : ∀ k' ∈ es, k' ≠ k := fun k' h e => hnd.1 (e ▸ h)
    obtain ⟨m, hmdef⟩ : ∃ m, (4 - cells.length + 1) * 2 ^ es.length = m := ⟨_, rfl⟩
    have hm : 0 < m := hmdef ▸ Nat.mul_pos (by omega) (Nat.two_pow_pos _)
    by_cases hsmall : run.length ≤ m
    · exact viaCols es hv hi hj hij hne hb hl hci hcj hnd.2 hes' (hmdef ▸ hsmall)
    have hlen' : run.length ≤ 2 * m := by
      simp only [length_cons, Nat.pow_succ, ← Nat.mul_assoc, hmdef] at hlen; omega
    -- split the run: `top` (at most `m` cards) parks in column `k`, `bot` (`m` cards) goes first
    obtain ⟨n, hn⟩ : ∃ n, run.length - m = n := ⟨_, rfl⟩
    obtain ⟨top, htop⟩ : ∃ top, run.take n = top := ⟨_, rfl⟩
    obtain ⟨bot, hbot⟩ : ∃ bot, run.drop n = bot := ⟨_, rfl⟩
    have hrun : top ++ bot = run := htop ▸ hbot ▸ take_append_drop n run
    have htop_len : top.length = n := by rw [← htop, length_take]; omega
    have hbot_len : bot.length = m := by rw [← hbot, length_drop]; omega
    have htop_ne : top ≠ [] := fun e => by rw [e] at htop_len; simp at htop_len; omega
    have hbot_ne : bot ≠ [] := fun e => by rw [e] at hbot_len; simp at hbot_len; omega
    rw [← hrun] at hb hl hci ⊢
    have hbtop : Built top := hb.of_append_left
    have hbbot : Built bot := hb.of_append_right
    have hlbot : Lands bot dest := by
      intro c hc p hp; apply hl c _ p hp
      rw [getLast?_append, hc]; rfl
    obtain ⟨b, bs, hbbs⟩ : ∃ b bs, bot = b :: bs := exists_cons_of_ne_nil hbot_ne
    have hltop : Lands top (bot ++ dest) := by
      intro c hc p hp
      rw [hbbs] at hp hb; simp at hp; subst hp
      exact hb.link c hc
    have hilt : i < cols.length := lt_of_getElem?_eq_some hci
    have hklt : k < cols.length := lt_of_getElem?_eq_some hck
    have hjlt : j < cols.length := lt_of_getElem?_eq_some hcj
    -- A. park `top` in the empty column `k`
    have hA := viaCols es (run := top) (rest := bot ++ rest) (dest := []) hv hi hk (Ne.symm hki)
      htop_ne hbtop (by intro c _ p hp; simp at hp) (by rw [hci, append_assoc])
      hck hnd.2 (fun k' h => ⟨(hes' k' h).1, (hes' k' h).2.1, hkes k' h, (hes' k' h).2.2.2⟩)
      (by rw [htop_len, hmdef]; omega)
    let colsA := (cols.set i (bot ++ rest)).set k (top ++ [])
    have hvA := hA.valid hv
    -- B. move `bot` onto the destination
    have hB := viaCols es (cols := colsA) (run := bot) (rest := rest) (dest := dest) hvA hi hj hij
      hbot_ne hbbot hlbot
      (by simp only [colsA]; rw [getElem?_set_ne hki]; simp [hilt])
      (by simp only [colsA]; rw [getElem?_set_ne hkj, getElem?_set_ne hij]; exact hcj)
      hnd.2
      (fun k' h => by
        obtain ⟨h1, h2, h3, h4⟩ := hes' k' h
        refine ⟨h1, h2, h3, ?_⟩
        simp only [colsA]
        rw [getElem?_set_ne (Ne.symm (hkes k' h)), getElem?_set_ne (Ne.symm h2)]; exact h4)
      (by rw [hbot_len, hmdef]; exact Nat.le_refl _)
    let colsB := (colsA.set i rest).set j (bot ++ dest)
    have hvB := hB.valid hvA
    -- C. move `top` from column `k` onto `bot`
    have hC := viaCols es (cols := colsB) (run := top) (rest := []) (dest := bot ++ dest) hvB hk hj hkj
      htop_ne hbtop hltop
      (by simp only [colsB, colsA]; rw [getElem?_set_ne (Ne.symm hkj), getElem?_set_ne (Ne.symm hki)]
          simp [hklt])
      (by simp [colsB, colsA, hjlt])
      hnd.2
      (fun k' h => by
        obtain ⟨h1, h2, h3, h4⟩ := hes' k' h
        refine ⟨h1, hkes k' h, h3, ?_⟩
        simp only [colsB, colsA]
        rw [getElem?_set_ne (Ne.symm h3), getElem?_set_ne (Ne.symm h2),
          getElem?_set_ne (Ne.symm (hkes k' h)), getElem?_set_ne (Ne.symm h2)]; exact h4)
      (by rw [htop_len, hmdef]; omega)
    have heq : (colsB.set k []).set j (top ++ (bot ++ dest)) = (cols.set i rest).set j (top ++ bot ++ dest) := by
      apply ext_getElem?; intro x
      simp only [colsB, colsA, getElem?_set, length_set]
      by_cases hxj : j = x
      · subst hxj; simp [hjlt]
      · by_cases hxk : k = x
        · subst hxk
          have hck' : cols[k]'hklt = [] := by simpa [hklt] using hck
          simp [hxj, Ne.symm hki, hck', hklt]
        · by_cases hxi : i = x
          · subst hxi; simp [hxj, hxk]
          · simp [hxj, hxk, hxi]
    rw [heq] at hC
    exact (hA.trans hB).trans hC

/-! ## Main theorems -/

/-- **Supermoves are shorthand**: every supermove from a valid position is a sequence of single-card moves. -/
theorem Supermove.reachable {s t : State} (hv : s.Valid) (h : Supermove s t) : Reachable s t := by
  obtain ⟨i, j, run, rest, dest, hi, hj, hij, hne, hci, hcj, hb, hl, hlen, rfl⟩ := h
  obtain ⟨cols, cells, home⟩ := s
  refine viaCols (emptyCols ⟨cols, cells, home⟩ i j) hv hi hj hij hne hb hl hci hcj
    ((nodup_range).filter _) (fun k hk => ?_) hlen
  simp only [emptyCols, mem_filter, mem_range, decide_eq_true_eq] at hk
  exact ⟨hk.1, hk.2⟩

theorem SuperReachable.reachable {s t : State} (hv : s.Valid) (h : SuperReachable s t) :
    Reachable s t := by
  induction h with
  | refl => exact .refl
  | tail _ hst ih =>
    rcases hst with hst | hst
    · exact .tail ih hst
    · exact ih.trans (hst.reachable (ih.valid hv))

theorem Reachable.superReachable {s t : State} (h : Reachable s t) : SuperReachable s t := by
  induction h with
  | refl => exact .refl
  | tail _ hst ih => exact .tail ih (.inl hst)

/-- **Supermoves change no reachability question** (hence no winnability question) from a valid position. -/
theorem superReachable_iff {s t : State} (hv : s.Valid) : SuperReachable s t ↔ Reachable s t :=
  ⟨SuperReachable.reachable hv, Reachable.superReachable⟩

end FreeCell

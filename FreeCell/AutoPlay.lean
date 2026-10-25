import FreeCell.Supermove

/-!
# Safe automatic foundation moves

Microsoft FreeCell, like many implementations, plays some foundation moves
automatically (its exact rule is not formalised here). This file proves that playing a *safe* foundation move never
turns a winnable position into an unwinnable one, and never lengthens the
shortest win. A card is safe to send home when it is an ace or a two, or when
both foundations of the opposite colour have reached at least one rank below it:
then every card that could still be stacked on it is either already home or an
ace, which can go home itself.

Consequently a game that forces any policy of safe automatic moves after every
move (`autoWinnable_iff`) wins exactly the positions that standard FreeCell wins.

The proof is a simulation (`Sim`): the position after the safe move tracks the
original winning line with some cards *absorbed* — already home in the
simulated position, but still in play in the original one. Absorbed cards of
each suit are the ranks just above the original foundation. Moves of absorbed
cards are skipped; every other move is replayed, except that an ace put onto an
absorbed two goes home instead (and becomes absorbed).
-/

namespace FreeCell

open List

/-! ## Definitions -/

/-- `c` is exposed in `s`, can go home now, and is safe to send home: an ace or a two,
or both opposite-colour foundations are at least one rank below it. -/
def SafeHome (s : State) (c : Card) : Prop :=
  (∃ src u, Pick s src c u) ∧ s.home[c.suit]? = some (c.rank - 1) ∧ 1 ≤ c.rank ∧
    (c.rank ≤ 2 ∨ ∀ su < 4, (Card.mk 0 su).red ≠ c.red → c.rank ≤ s.home.getD su 0 + 1)

/-- One safe foundation move: card `c` goes home from `src` and `SafeHome s c` holds. -/
def SafeStep (s t : State) : Prop :=
  ∃ src c u, Pick s src c u ∧ Put u src c .home t ∧ SafeHome s c

/-- Zero or more safe foundation moves. -/
inductive SafeChain : State → State → Prop
  | refl {s : State} : SafeChain s s
  | head {s t u : State} : SafeStep s t → SafeChain t u → SafeChain s u

/-- Some reachable position is won. -/
def Winnable (s : State) : Prop := ∃ t, Reachable s t ∧ t.Won

/-- `WinsIn n s`: `s` can be won in at most `n` moves. -/
inductive WinsIn : Nat → State → Prop
  | won {n : Nat} {s : State} : s.Won → WinsIn n s
  | step {n : Nat} {s t : State} : Step s t → WinsIn n t → WinsIn (n + 1) s

/-- One move of the auto-play game: a legal move followed by the policy's automatic moves. -/
def AutoStep (auto : State → State) (s t : State) : Prop := ∃ u, Step s u ∧ t = auto u

inductive AutoReach (auto : State → State) : State → State → Prop
  | refl {s : State} : AutoReach auto s s
  | head {s t u : State} : AutoStep auto s t → AutoReach auto t u → AutoReach auto s u

/-- The auto-play game, from position `s`, reaches a won position. -/
def AutoWinnable (auto : State → State) (s : State) : Prop := ∃ t, AutoReach auto s t ∧ t.Won

/-! ## Basic facts -/

theorem SafeStep.legal {s t : State} (h : SafeStep s t) : ∃ src, Legal s ⟨src, .home⟩ t :=
  let ⟨src, c, u, hp, hq, _⟩ := h; ⟨src, c, u, hp, hq⟩

theorem SafeStep.step {s t : State} (h : SafeStep s t) : Step s t :=
  let ⟨_, hl⟩ := h.legal; ⟨_, hl⟩

/-- `SafeHome` is not vacuous: a safe card can be played home. -/
theorem SafeHome.exists_safeStep {s : State} {c : Card} (h : SafeHome s c) : ∃ t, SafeStep s t := by
  obtain ⟨⟨src, u, hp⟩, hh, h1, _⟩ := h
  have hu : u.home = s.home := by cases hp <;> rfl
  exact ⟨_, src, c, u, hp, Put.home (h := c.rank - 1) (by rw [hu]; exact hh) (by omega),
    ⟨src, u, hp⟩, hh, h1, ‹_›⟩

theorem SafeChain.reachable {s t : State} (h : SafeChain s t) : Reachable s t := by
  induction h with
  | refl => exact .refl
  | head hst _ ih => exact (Reachable.single hst.step).trans ih

theorem WinsIn.mono {n m : Nat} {s : State} (h : WinsIn n s) (hnm : n ≤ m) : WinsIn m s := by
  induction h generalizing m with
  | won hw => exact .won hw
  | step hst _ ih =>
    obtain ⟨m, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    exact .step hst (ih (by omega))

theorem WinsIn.winnable {n : Nat} {s : State} (h : WinsIn n s) : Winnable s := by
  induction h with
  | won hw => exact ⟨_, .refl, hw⟩
  | step hst _ ih =>
    obtain ⟨t, hr, hw⟩ := ih
    exact ⟨t, (Reachable.single hst).trans hr, hw⟩

theorem Winnable.winsIn {s : State} (h : Winnable s) : ∃ n, WinsIn n s := by
  obtain ⟨t, hr, hw⟩ := h
  suffices ∀ n, WinsIn n t → ∃ m, WinsIn m s from this 0 (.won hw)
  clear hw
  induction hr with
  | refl => exact fun n h => ⟨n, h⟩
  | tail _ hst ih => exact fun n h => ih (n + 1) (.step hst h)

theorem winnable_iff_winsIn {s : State} : Winnable s ↔ ∃ n, WinsIn n s :=
  ⟨Winnable.winsIn, fun ⟨_, h⟩ => h.winnable⟩

/-! ## List helpers -/

theorem getD_set_self {l : List Nat} {i a : Nat} (h : i < l.length) : (l.set i a).getD i 0 = a := by
  simp [getD_eq_getElem?_getD, h]

theorem getD_set_ne {l : List Nat} {i k a : Nat} (h : i ≠ k) : (l.set i a).getD k 0 = l.getD k 0 := by
  simp [getD_eq_getElem?_getD, getElem?_set_ne h]

theorem getD_of_getElem? {l : List Nat} {i a : Nat} (h : l[i]? = some a) : l.getD i 0 = a := by
  simp [getD_eq_getElem?_getD, h]

theorem filter_erase_of_false {p : Card → Bool} {a : Card} (ha : p a = false) :
    ∀ l : List Card, (l.erase a).filter p = l.filter p
  | [] => rfl
  | d :: ds => by
    by_cases hd : d = a
    · subst hd; simp [ha]
    · rw [erase_cons_tail (by simpa using hd)]
      simp only [filter_cons]; rw [filter_erase_of_false ha ds]

theorem erase_filter_of_true {p : Card → Bool} {a : Card} (ha : p a = true) :
    ∀ l : List Card, (l.filter p).erase a = (l.erase a).filter p
  | [] => rfl
  | d :: ds => by
    by_cases hd : d = a
    · subst hd; simp [ha]
    · rw [erase_cons_tail (by simpa using hd)]
      simp only [filter_cons]
      split
      · rw [erase_cons_tail (by simpa using hd), erase_filter_of_true ha ds]
      · exact erase_filter_of_true ha ds

theorem filter_insertSorted_of_false {p : Card → Bool} {a : Card} (ha : p a = false) :
    ∀ l : List Card, (insertSorted a l).filter p = l.filter p
  | [] => by simp [insertSorted, ha]
  | d :: ds => by
    simp only [insertSorted]
    split
    · simp [ha]
    · simp only [filter_cons]; rw [filter_insertSorted_of_false ha ds]

theorem insertSorted_of_le {a : Card} : ∀ {l : List Card}, (∀ e ∈ l, a.code ≤ e.code) →
    insertSorted a l = a :: l
  | [], _ => rfl
  | d :: ds, h => by simp [insertSorted, h d (mem_cons_self ..)]

theorem filter_insertSorted_of_true {p : Card → Bool} {a : Card} (ha : p a = true) :
    ∀ {l : List Card}, l.Pairwise (fun x y => x.code < y.code) →
      (insertSorted a l).filter p = insertSorted a (l.filter p)
  | [], _ => by simp [insertSorted, ha]
  | d :: ds, hs => by
    rw [pairwise_cons] at hs
    simp only [insertSorted]
    split
    · rename_i hle
      rw [filter_cons_of_pos ha, insertSorted_of_le]
      intro e he
      simp only [mem_filter, mem_cons] at he
      rcases he.1 with rfl | he1
      · exact hle
      · have := hs.1 e he1; omega
    · rename_i hgt
      simp only [filter_cons]
      split
      · simp only [insertSorted, hgt, ite_false, filter_insertSorted_of_true ha hs.2]
      · exact filter_insertSorted_of_true ha hs.2

theorem set_of_getElem? {α : Type _} {l : List α} {i : Nat} {a : α} (h : l[i]? = some a) :
    l.set i a = l := by
  obtain ⟨hlt, rfl⟩ := List.getElem?_eq_some_iff.mp h
  exact set_getElem_self hlt

/-- Replacing a column by one with the same filtered contents leaves the filtered columns alone. -/
theorem map_filter_set {f : Card → Bool} {cols : List (List Card)} {i : Nat} {a b : List Card}
    (h : cols[i]? = some a) (hab : b.filter f = a.filter f) :
    (cols.set i b).map (filter f) = cols.map (filter f) := by
  rw [map_set, hab]
  apply set_of_getElem?
  simp [h]

theorem filter_const_true : ∀ l : List Card, l.filter (fun _ => true) = l
  | [] => rfl
  | d :: ds => by rw [filter_cons_of_pos rfl, filter_const_true ds]

theorem filter_congr_of_not_mem {f g : Card → Bool} {x : Card} (hfg : ∀ y, y ≠ x → f y = g y)
    {l : List Card} (hx : x ∉ l) : l.filter f = l.filter g :=
  filter_congr fun y hy => hfg y (fun e => hx (e ▸ hy))

theorem map_filter_congr_of_not_mem {f g : Card → Bool} {x : Card} (hfg : ∀ y, y ≠ x → f y = g y)
    {cols : List (List Card)} (hx : x ∉ cols.flatten) : cols.map (filter f) = cols.map (filter g) :=
  map_congr_left fun col hcol =>
    filter_congr_of_not_mem hfg (fun h => hx (mem_flatten.mpr ⟨col, hcol, h⟩))

/-! ## Facts about a lifted card -/

theorem mem_homeCards {home : List Nat} {y : Card} :
    y ∈ homeCards home ↔ y.suit < 4 ∧ 1 ≤ y.rank ∧ y.rank ≤ home.getD y.suit 0 := by
  obtain ⟨r, su⟩ := y
  simp only [homeCards, mem_flatMap, mem_range, mem_map, Card.mk.injEq]
  constructor
  · rintro ⟨su', hsu, r', hr, rfl, rfl⟩; omega
  · rintro ⟨hsu, h1, h2⟩; exact ⟨su, hsu, r - 1, by omega, by omega, rfl⟩

theorem Pick.home_eq {s : State} {src : Src} {c : Card} {u : State} (h : Pick s src c u) :
    u.home = s.home := by cases h <;> rfl

theorem Pick.cells_sublist {s : State} {src : Src} {c : Card} {u : State} (h : Pick s src c u) :
    u.cells <+ s.cells := by
  cases h with
  | col => exact Sublist.refl _
  | cell => exact erase_sublist

/-- The lifted card appears nowhere else in the position. -/
theorem Pick.not_mem {s : State} {src : Src} {c : Card} {u : State} (hv : s.Valid)
    (h : Pick s src c u) : c ∉ u.cols.flatten ∧ c ∉ u.cells ∧ c ∉ homeCards u.home := by
  have hnd : (c :: u.cards).Nodup := h.cards_perm.nodup_iff.mp hv.nodup
  have hc : c ∉ u.cards := (nodup_cons.mp hnd).1
  simp only [State.cards, mem_append, not_or] at hc
  exact ⟨hc.1.1, hc.1.2, hc.2⟩

/-- The lifted card is above its foundation. -/
theorem Pick.home_lt {s : State} {src : Src} {c : Card} {u : State} (hv : s.Valid)
    (h : Pick s src c u) : s.home.getD c.suit 0 < c.rank := by
  have hc := mem_deck.mp (hv.mem_deck h.mem_cards)
  have := (h.not_mem hv).2.2
  rw [h.home_eq, mem_homeCards] at this
  omega

theorem lt_length_of_getElem? {l : List Nat} {i a : Nat} (h : l[i]? = some a) : i < l.length :=
  lt_of_getElem?_eq_some h

theorem getElem?_eq_getD {l : List Nat} {i : Nat} (h : i < l.length) : l[i]? = some (l.getD i 0) := by
  simp [getD_eq_getElem?_getD, h]

/-! ## The simulation -/

/-- A card still in play in the original position but already home in the simulated one:
its rank lies above the original foundation height `h` and at most the simulated one `h'`. -/
def kept (h h' : List Nat) (y : Card) : Bool :=
  !decide (h.getD y.suit 0 < y.rank ∧ y.rank ≤ h'.getD y.suit 0)

theorem kept_eq_false {h h' : List Nat} {y : Card} :
    kept h h' y = false ↔ h.getD y.suit 0 < y.rank ∧ y.rank ≤ h'.getD y.suit 0 := by
  simp [kept]

/-- `Sim t t'`: the simulated position `t'` is `t` with its absorbed cards sent home, and every
card that could be stacked on an absorbed card is home in `t` or an ace. -/
structure Sim (t t' : State) : Prop where
  cols : t'.cols = t.cols.map (filter (kept t.home t'.home))
  cells : t'.cells = t.cells.filter (kept t.home t'.home)
  home_length : t'.home.length = t.home.length
  home_le : ∀ su, t.home.getD su 0 ≤ t'.home.getD su 0
  parent : ∀ p y, kept t.home t'.home p = false → y.suit < 4 → Fits y p →
    y.rank = 1 ∨ y.rank ≤ t.home.getD y.suit 0

/-- Lifting an absorbed card leaves the filtered columns and cells unchanged. -/
theorem pick_filter {F : Card → Bool} {t v : State} {src : Src} {x : Card} (hx : F x = false)
    (hp : Pick t src x v) :
    t.cols.map (filter F) = v.cols.map (filter F) ∧ t.cells.filter F = v.cells.filter F := by
  cases hp with
  | col _ hcol => exact ⟨(map_filter_set hcol (by simp [hx])).symm, rfl⟩
  | cell _ => exact ⟨rfl, (filter_erase_of_false hx _).symm⟩

/-- Putting an absorbed card anywhere but home leaves the filtered columns and cells unchanged. -/
theorem put_filter {F : Card → Bool} {v u : State} {src : Src} {x : Card} {dst : Dst}
    (hx : F x = false) (hq : Put v src x dst u) (hd : dst ≠ .home) :
    v.cols.map (filter F) = u.cols.map (filter F) ∧ v.cells.filter F = u.cells.filter F ∧
      u.home = v.home := by
  cases hq with
  | home => exact absurd rfl hd
  | empty _ _ he => exact ⟨(map_filter_set he (by simp [hx])).symm, rfl, rfl⟩
  | stack _ _ hp _ _ => exact ⟨(map_filter_set hp (by simp [hx])).symm, rfl, rfl⟩
  | cell _ => exact ⟨rfl, (filter_insertSorted_of_false hx _).symm, rfl⟩

/-- A kept card can be lifted in the simulated position too. -/
theorem sim_pick {F : Card → Bool} {t t' v : State} {src : Src} {x : Card} (hx : F x = true)
    (hp : Pick t src x v) (hc : t'.cols = t.cols.map (filter F))
    (hl : t'.cells = t.cells.filter F) :
    ∃ v', Pick t' src x v' ∧ v'.cols = v.cols.map (filter F) ∧ v'.cells = v.cells.filter F ∧
      v'.home = t'.home := by
  cases hp with
  | col hi hcol =>
    rename_i i rest
    refine ⟨_, Pick.col (rest := rest.filter F) hi ?_, ?_, hl, rfl⟩
    · rw [hc, getElem?_map, hcol]; simp [hx]
    · simp only [hc, map_set]
  | cell hm =>
    refine ⟨_, Pick.cell (hl ▸ mem_filter.mpr ⟨hm, hx⟩), hc, ?_, rfl⟩
    simp only [hl]; exact erase_filter_of_true hx _

theorem parent_mono {t t' u u' : State} (hs : Sim t t') (hle : ∀ su, t.home.getD su 0 ≤ u.home.getD su 0)
    (hsub : ∀ p, kept u.home u'.home p = false → kept t.home t'.home p = false) :
    ∀ p y, kept u.home u'.home p = false → y.suit < 4 → Fits y p →
      y.rank = 1 ∨ y.rank ≤ u.home.getD y.suit 0 := by
  intro p y hp hy hf
  rcases hs.parent p y (hsub p hp) hy hf with h | h
  · exact .inl h
  · exact .inr (Nat.le_trans h (hle _))

theorem Sim.of_home {t t' u u' : State} (hs : Sim t t') (hu : u.home = t.home) (hu' : u'.home = t'.home)
    (hc : u'.cols = u.cols.map (filter (kept t.home t'.home)))
    (hl : u'.cells = u.cells.filter (kept t.home t'.home)) : Sim u u' := by
  obtain ⟨cols, cells, home⟩ := u
  obtain ⟨cols', cells', home'⟩ := u'
  dsimp only at hu hu' hc hl
  subst hu hu'
  exact ⟨hc, hl, hs.home_length, hs.home_le, hs.parent⟩

theorem card_eq {x y : Card} (hs : y.suit = x.suit) (hr : y.rank = x.rank) : y = x := by
  cases x; cases y; simp_all

/-- **Simulation step.** Each move of the original line is skipped or matched by one move. -/
theorem Sim.step {t t' u : State} (hv : t.Valid) (hs : Sim t t') (hst : Step t u) :
    Sim u t' ∨ ∃ u', Step t' u' ∧ Sim u u' := by
  obtain ⟨⟨src, dst⟩, x, v, hp, hq⟩ := hst
  dsimp only at hp hq
  have hxd := mem_deck.mp (hv.mem_deck hp.mem_cards)
  have hlt := hp.home_lt hv
  obtain ⟨hnc, hnl, -⟩ := hp.not_mem hv
  have hvh := hp.home_eq
  have hlen4 := hv.home_length
  by_cases hx : kept t.home t'.home x = true
  · -- a kept card: replay the move (an ace onto an absorbed two goes home instead)
    right
    obtain ⟨v', hp', hvc, hvl, hvh'⟩ := sim_pick hx hp hs.cols hs.cells
    cases hq with
    | home hh hr =>
      rename_i h
      rw [hvh] at hh
      have hgd := getD_of_getElem? hh
      have hsu : x.suit < t.home.length := lt_length_of_getElem? hh
      have ht' : t'.home.getD x.suit 0 = h := by
        have := hs.home_le x.suit
        have : ¬ (t.home.getD x.suit 0 < x.rank ∧ x.rank ≤ t'.home.getD x.suit 0) :=
          fun h' => by rw [← kept_eq_false] at h'; simp [hx] at h'
        omega
      have hh' : v'.home[x.suit]? = some h := by
        rw [hvh', getElem?_eq_getD (by rw [hs.home_length]; exact hsu), ht']
      refine ⟨_, ⟨⟨src, .home⟩, x, v', hp', Put.home hh' hr⟩, ?_⟩
      have hF : kept (v.home.set x.suit x.rank) (v'.home.set x.suit x.rank) = kept t.home t'.home := by
        funext y
        rw [hvh, hvh']
        simp only [kept]
        by_cases hy : x.suit = y.suit
        · rw [← hy, getD_set_self hsu, getD_set_self (by rw [hs.home_length]; exact hsu), hgd, ht']
          congr 1; simp only [decide_eq_decide]; omega
        · rw [getD_set_ne hy, getD_set_ne hy]
      refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp only [hF]
      · exact hvc
      · exact hvl
      · simp [hvh, hvh', hs.home_length]
      · intro su
        rw [hvh, hvh']
        by_cases hy : x.suit = su
        · subst hy; rw [getD_set_self hsu, getD_set_self (by rw [hs.home_length]; exact hsu)]; omega
        · rw [getD_set_ne hy, getD_set_ne hy]; exact hs.home_le su
      · intro p y hp hy hf
        rcases hs.parent p y hp hy hf with h1 | h1
        · exact .inl h1
        · refine .inr (Nat.le_trans h1 ?_)
          rw [hvh]
          by_cases hy : x.suit = y.suit
          · rw [← hy, getD_set_self hsu]; omega
          · rw [getD_set_ne hy]; exact Nat.le_refl _
    | empty hj hsrc he =>
      rename_i j
      have he' : v'.cols[j]? = some [] := by rw [hvc, getElem?_map, he]; rfl
      refine ⟨_, ⟨⟨src, .col j⟩, x, v', hp', Put.empty hj hsrc he'⟩, ?_⟩
      refine hs.of_home hvh hvh' ?_ hvl
      simp only [hvc, map_set]; simp [hx]
    | stack hj hsrc hpp hr hcol =>
      rename_i p ps j
      by_cases hk : kept t.home t'.home p = true
      · have hpp' : v'.cols[j]? = some (p :: ps.filter (kept t.home t'.home)) := by
          rw [hvc, getElem?_map, hpp]; simp [hk]
        refine ⟨_, ⟨⟨src, .col j⟩, x, v', hp', Put.stack hj hsrc hpp' hr hcol⟩, ?_⟩
        refine hs.of_home hvh hvh' ?_ hvl
        simp only [hvc, map_set]; simp [hx, hk]
      · -- the parent is absorbed, so `x` is an ace: send it home instead
        have hk' : kept t.home t'.home p = false := by simpa using hk
        have hace : x.rank = 1 := by
          rcases hs.parent p x hk' hxd.2.2 ⟨hr, hcol⟩ with h | h
          · exact h
          · omega
        have hsu : x.suit < t.home.length := by omega
        have hsu' : x.suit < t'.home.length := by rw [hs.home_length]; exact hsu
        have ht0 : t.home.getD x.suit 0 = 0 := by omega
        have ht'0 : t'.home.getD x.suit 0 = 0 := by
          have : ¬ (t.home.getD x.suit 0 < x.rank ∧ x.rank ≤ t'.home.getD x.suit 0) :=
            fun h' => by rw [← kept_eq_false] at h'; simp [hx] at h'
          omega
        have hh' : v'.home[x.suit]? = some 0 := by rw [hvh', getElem?_eq_getD hsu', ht'0]
        refine ⟨_, ⟨⟨src, .home⟩, x, v', hp', Put.home hh' (by omega)⟩, ?_⟩
        have hF : ∀ y, y ≠ x → kept v.home (v'.home.set x.suit x.rank) y = kept t.home t'.home y := by
          intro y hyx
          rw [hvh, hvh']
          simp only [kept]
          by_cases hy : x.suit = y.suit
          · rw [← hy, getD_set_self hsu', ht0, ht'0]
            have : y.rank ≠ 1 := fun h => hyx (card_eq hy.symm (by omega))
            congr 1; simp only [decide_eq_decide]; omega
          · rw [getD_set_ne hy]
        have hFx : kept v.home (v'.home.set x.suit x.rank) x = false := by
          rw [kept_eq_false, hvh, hvh', getD_set_self hsu', ht0]; omega
        refine ⟨?_, ?_, ?_, ?_, ?_⟩
        · show v'.cols = (v.cols.set j (x :: p :: ps)).map _
          rw [map_filter_set hpp (by simp [hFx]), hvc]
          exact (map_filter_congr_of_not_mem hF hnc).symm
        · show v'.cells = v.cells.filter _
          rw [hvl]; exact (filter_congr_of_not_mem hF hnl).symm
        · simp [hvh, hvh', hs.home_length]
        · intro su
          show v.home.getD su 0 ≤ (v'.home.set x.suit x.rank).getD su 0
          rw [hvh, hvh']
          by_cases hy : x.suit = su
          · subst hy; rw [ht0]; omega
          · rw [getD_set_ne hy]; exact hs.home_le su
        · intro p0 y hp0 hy hf
          show y.rank = 1 ∨ y.rank ≤ v.home.getD y.suit 0
          rw [hvh]
          by_cases hpx : p0 = x
          · subst hpx; have := hf.1; omega
          · exact hs.parent p0 y (by rw [← hF p0 hpx]; exact hp0) hy hf
    | cell hl =>
      have hl' : v'.cells.length < 4 := by
        rw [hvl]; exact Nat.lt_of_le_of_lt (length_filter_le _ _) hl
      refine ⟨_, ⟨⟨_, .cell⟩, x, v', hp', Put.cell hl'⟩, ?_⟩
      refine hs.of_home hvh hvh' hvc ?_
      show insertSorted x v'.cells = (insertSorted x v.cells).filter _
      rw [hvl, filter_insertSorted_of_true hx (hv.cells_sorted.sublist hp.cells_sublist)]
  · -- an absorbed card: skip the move
    left
    have hx' : kept t.home t'.home x = false := by simpa using hx
    obtain ⟨hc1, hl1⟩ := pick_filter hx' hp
    by_cases hd : dst = .home
    · subst hd
      cases hq with
      | home hh hr =>
        rename_i h
        rw [hvh] at hh
        have hgd := getD_of_getElem? hh
        have hsu : x.suit < t.home.length := lt_length_of_getElem? hh
        have hF : ∀ y, y ≠ x → kept (v.home.set x.suit x.rank) t'.home y = kept t.home t'.home y := by
          intro y hyx
          rw [hvh]
          simp only [kept]
          by_cases hy : x.suit = y.suit
          · rw [← hy, getD_set_self hsu, hgd]
            have : y.rank ≠ x.rank := fun h => hyx (card_eq hy.symm h)
            congr 1; simp only [decide_eq_decide]; omega
          · rw [getD_set_ne hy]
        have hle : ∀ su, t.home.getD su 0 ≤ (v.home.set x.suit x.rank).getD su 0 := by
          intro su
          rw [hvh]
          by_cases hy : x.suit = su
          · subst hy; rw [getD_set_self hsu]; omega
          · rw [getD_set_ne hy]; exact Nat.le_refl _
        refine ⟨?_, ?_, ?_, ?_, ?_⟩
        · show t'.cols = v.cols.map _
          rw [hs.cols, hc1]; exact map_filter_congr_of_not_mem (fun y h => (hF y h).symm) hnc
        · show t'.cells = v.cells.filter _
          rw [hs.cells, hl1]; exact filter_congr_of_not_mem (fun y h => (hF y h).symm) hnl
        · simp [hvh, hs.home_length]
        · intro su
          show (v.home.set x.suit x.rank).getD su 0 ≤ _
          rw [hvh]
          by_cases hy : x.suit = su
          · subst hy; rw [getD_set_self hsu]; exact (kept_eq_false.mp hx').2
          · rw [getD_set_ne hy]; exact hs.home_le su
        · refine parent_mono hs hle (fun p hp => ?_)
          dsimp only at hp
          rw [kept_eq_false] at hp ⊢
          have := hle p.suit; omega
    · obtain ⟨hc2, hl2, hh2⟩ := put_filter hx' hq hd
      refine hs.of_home (hh2.trans hvh) rfl ?_ ?_
      · rw [hs.cols, hc1, hc2]
      · rw [hs.cells, hl1, hl2]

/-- The position after a safe move simulates the position before it, with the moved card absorbed. -/
theorem Sim.init {s s' : State} (hv : s.Valid) (h : SafeStep s s') : Sim s s' := by
  obtain ⟨src, c, v, hp, hq, -, -, -, hsafe⟩ := h
  obtain ⟨hnc, hnl, -⟩ := hp.not_mem hv
  have hvh := hp.home_eq
  cases hq with
  | home hh hr =>
    rename_i h0
    rw [hvh] at hh
    have hgd := getD_of_getElem? hh
    have hsu : c.suit < s.home.length := lt_length_of_getElem? hh
    have hF : ∀ y, kept s.home (v.home.set c.suit c.rank) y = false ↔ y = c := by
      intro y
      rw [kept_eq_false, hvh]
      by_cases hy : c.suit = y.suit
      · rw [← hy, getD_set_self hsu, hgd]
        constructor
        · intro h; exact card_eq hy.symm (by omega)
        · rintro rfl; omega
      · rw [getD_set_ne hy]
        constructor
        · omega
        · rintro rfl; exact absurd rfl hy
    have hF' : ∀ y, y ≠ c → kept s.home (v.home.set c.suit c.rank) y = (fun _ => true) y := by
      intro y hy
      cases hk : kept s.home (v.home.set c.suit c.rank) y
      · exact absurd ((hF y).mp hk) hy
      · rfl
    obtain ⟨hc1, hl1⟩ := pick_filter ((hF c).mpr rfl) hp
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · show v.cols = _
      rw [hc1, map_filter_congr_of_not_mem hF' hnc]
      exact ((map_congr_left fun l _ => filter_const_true l).trans (map_id' _)).symm
    · show v.cells = _
      rw [hl1, filter_congr_of_not_mem hF' hnl]; exact (filter_const_true _).symm
    · simp [hvh]
    · intro su
      show _ ≤ (v.home.set c.suit c.rank).getD su 0
      rw [hvh]
      by_cases hy : c.suit = su
      · subst hy; rw [getD_set_self hsu]; omega
      · rw [getD_set_ne hy]; exact Nat.le_refl _
    · intro p y hp' hy hf
      have hpc : p = c := (hF p).mp hp'
      subst hpc
      obtain ⟨hf1, hf2⟩ := hf
      rcases hsafe with h2 | hopp
      · omega
      · have := hopp y.suit hy (fun e => hf2 e.symm)
        omega

theorem Sim.won {t t' : State} (hs : Sim t t') (hv' : t'.Valid) (hw : t.Won) : t'.Won := by
  have h0 := hs.home_le 0
  have h1 := hs.home_le 1
  have h2 := hs.home_le 2
  have h3 := hs.home_le 3
  have hl := hv'.home_length
  have hle := hv'.home_le
  unfold State.Won at hw ⊢
  rw [hw] at h0 h1 h2 h3
  generalize t'.home = l at *
  match l, hl with
  | [a, b, c, d], _ =>
    have ha := hle a (by simp)
    have hb := hle b (by simp)
    have hc := hle c (by simp)
    have hd := hle d (by simp)
    simp only [getD_eq_getElem?_getD] at h0 h1 h2 h3
    simp only [getElem?_cons_zero, getElem?_cons_succ, Option.getD_some] at h0 h1 h2 h3
    simp only [List.cons.injEq, and_true]
    omega

/-- A simulated position wins at least as fast as the position it simulates. -/
theorem Sim.winsIn {n : Nat} {t t' : State} (hv : t.Valid) (hv' : t'.Valid) (hs : Sim t t')
    (h : WinsIn n t) : WinsIn n t' := by
  induction h generalizing t' with
  | won hw => exact .won (hs.won hv' hw)
  | step hst _ ih =>
    rcases hs.step hv hst with hs' | ⟨u', hst', hs'⟩
    · exact (ih (hst.valid hv) hv' hs').mono (by omega)
    · exact .step hst' (ih (hst.valid hv) (hst'.valid hv') hs')

/-! ## Safe moves preserve winnability -/

/-- **Safe foundation moves never hurt**: after a safe foundation move from a valid
position, the position can still be won, in at most as many moves as before. -/
theorem SafeStep.winsIn {n : Nat} {s s' : State} (hv : s.Valid) (h : SafeStep s s')
    (hw : WinsIn n s) : WinsIn n s' :=
  Sim.winsIn hv (h.step.valid hv) (Sim.init hv h) hw

theorem SafeStep.winnable {s s' : State} (hv : s.Valid) (h : SafeStep s s') (hw : Winnable s) :
    Winnable s' :=
  let ⟨_, hn⟩ := hw.winsIn; (h.winsIn hv hn).winnable

/-- A safe foundation move from a valid position changes no winnability question. -/
theorem SafeStep.winnable_iff {s s' : State} (hv : s.Valid) (h : SafeStep s s') :
    Winnable s' ↔ Winnable s :=
  ⟨fun ⟨t, hr, hw⟩ => ⟨t, (Reachable.single h.step).trans hr, hw⟩, h.winnable hv⟩

theorem SafeChain.valid {s s' : State} (hv : s.Valid) (h : SafeChain s s') : s'.Valid :=
  h.reachable.valid hv

theorem SafeChain.winsIn {n : Nat} {s s' : State} (hv : s.Valid) (h : SafeChain s s')
    (hw : WinsIn n s) : WinsIn n s' := by
  induction h with
  | refl => exact hw
  | head hst _ ih => exact ih (hst.step.valid hv) (hst.winsIn hv hw)

/-! ## Games with forced safe auto-play -/

theorem AutoReach.reachable {auto : State → State} (hauto : ∀ s, s.Valid → SafeChain s (auto s))
    {s t : State} (hv : s.Valid) (h : AutoReach auto s t) : Reachable s t := by
  induction h with
  | refl => exact .refl
  | head hst _ ih =>
    obtain ⟨u, hsu, rfl⟩ := hst
    have hu := hsu.valid hv
    have hr := (Reachable.single hsu).trans (hauto u hu).reachable
    exact hr.trans (ih (hr.valid hv))

/-- A position (already auto-played) that standard rules win in `n` moves is won by the auto-play game. -/
theorem autoWinnable_of_winsIn {auto : State → State} (hauto : ∀ s, s.Valid → SafeChain s (auto s)) :
    ∀ {n : Nat} {a : State}, a.Valid → WinsIn n a → AutoWinnable auto a
  | _, _, _, .won hw => ⟨_, .refl, hw⟩
  | _ + 1, _, hv, .step (t := u) hst hw => by
    have hu := hst.valid hv
    obtain ⟨t, hr, ht⟩ := autoWinnable_of_winsIn hauto ((hauto u hu).valid hu) ((hauto u hu).winsIn hu hw)
    exact ⟨t, .head ⟨u, hst, rfl⟩ hr, ht⟩

/-- **Forced safe auto-play changes no winnability question.** For any policy `auto` that only
plays safe foundation moves, the game that applies `auto` at the start and after every move
wins from a valid `start` exactly when standard FreeCell does. -/
theorem autoWinnable_iff {auto : State → State} (hauto : ∀ s, s.Valid → SafeChain s (auto s))
    {start : State} (hv : start.Valid) : AutoWinnable auto (auto start) ↔ Winnable start := by
  have h0 := hauto start hv
  constructor
  · rintro ⟨t, hr, hw⟩
    exact ⟨t, h0.reachable.trans (hr.reachable hauto (h0.valid hv)), hw⟩
  · intro hw
    obtain ⟨n, hn⟩ := hw.winsIn
    exact autoWinnable_of_winsIn hauto (h0.valid hv) (h0.winsIn hv hn)

/-! ## A concrete auto-play policy -/

/-- Executable safety test (the `safeHome` rule of `FreeCell.Propose`, minus the home check that
`put` performs). -/
def safeB (s : State) (c : Card) : Bool :=
  c.rank ≤ 2 || (List.range 4).all fun su =>
    (Card.mk 0 su).red == c.red || c.rank ≤ s.home.getD su 0 + 1

/-- The first safe foundation move: column tops in column order, then free cells. -/
def autoMove? (s : State) : Option State :=
  (colIdx.map Src.col ++ s.cells.map Src.cell).findSome? fun src =>
    match pick s src with
    | some (c, u) => if safeB s c then put u src c .home else none
    | none => none

/-- Play safe foundation moves until none is left (52 moves always suffice). -/
def autoPlay : Nat → State → State
  | 0, s => s
  | n + 1, s =>
    match autoMove? s with
    | some t => autoPlay n t
    | none => s

theorem autoMove?_safeStep {s t : State} (h : autoMove? s = some t) : SafeStep s t := by
  obtain ⟨src, -, hsrc⟩ := List.exists_of_findSome?_eq_some h
  split at hsrc
  · rename_i c u hpick
    split at hsrc
    · rename_i hsafe
      have hp := pick_eq_some_iff.mp hpick
      have hq := put_eq_some_iff.mp hsrc
      refine ⟨src, c, u, hp, hq, ⟨src, u, hp⟩, ?_⟩
      cases hq with
      | home hh hr =>
        rw [hp.home_eq] at hh
        refine ⟨by rw [hh]; congr 1; omega, by omega, ?_⟩
        simp only [safeB, Bool.or_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range,
          beq_iff_eq] at hsafe
        rcases hsafe with h2 | hall
        · exact .inl h2
        · exact .inr fun su hsu hred => (hall su hsu).resolve_left hred
    · simp at hsrc
  · simp at hsrc

theorem autoPlay_safeChain : ∀ (n : Nat) (s : State), SafeChain s (autoPlay n s)
  | 0, _ => .refl
  | n + 1, s => by
    simp only [autoPlay]
    split
    · rename_i t ht; exact .head (autoMove?_safeStep ht) (autoPlay_safeChain n t)
    · exact .refl

/-- **Forced safe auto-play, a concrete policy**: with `autoPlay 52` (play the first safe card,
columns then cells, repeatedly) forced at the start and after every move, exactly the
standard-winnable valid positions are won. Whether Microsoft's own rule is a safe policy in
this sense is not established here; `autoWinnable_iff` covers any rule that is. -/
theorem autoWinnable_autoPlay_iff {start : State} (hv : start.Valid) :
    AutoWinnable (autoPlay 52) (autoPlay 52 start) ↔ Winnable start :=
  autoWinnable_iff (fun s _ => autoPlay_safeChain 52 s) hv

end FreeCell

import FreeCell.Cert
import FreeCell.Finite
import FreeCell.Heuristic

/-!
# The verified reference search

A depth-first search over positions with a visited set compared by full
equality (`HashSet` with a lawful `BEq`: hashes only pick buckets, membership
is decided by `=`, so distinct positions are never merged).

Each stack frame carries the reversed move list that reached its position, so a
won successor yields a winning path without parent pointers. The invariant
`Inv` states:

* every visited position is reachable from the start and not won;
* every stack frame's moves replay from the start to its position;
* every visited position is either still pending on the stack or has all of
  its successors visited.

When the stack empties, the visited set is therefore a closed certificate.

`step` performs one expansion and returns either a checked `Outcome` or a new
search state with strictly smaller `Search.measure`. The measure is
`2 * (stateBound - visited) + pending`; it decreases because each expansion pops
one frame and pushes one frame per newly visited position, and the visited set
never exceeds the finite bound of `FreeCell.Finite`. `solve` iterates `step` by
well-founded recursion: it is total, with no fuel and no `partial`.
-/

namespace FreeCell

open Std

/-- A pending position and the reversed list of moves that reached it. -/
structure Frame where
  state : State
  path : List Move

structure Inv (start : State) (visited : HashSet State) (stack : List Frame) : Prop where
  start_mem : start ∈ visited
  reach : ∀ s, s ∈ visited → Reachable start s
  nowin : ∀ s, s ∈ visited → s.won = false
  stack_ok : ∀ f ∈ stack, f.state ∈ visited ∧ replay start f.path.reverse = some f.state
  closed : ∀ s, s ∈ visited → (∃ f ∈ stack, f.state = s) ∨ ∀ t ∈ moves s, t ∈ visited

structure Search (start : State) where
  visited : HashSet State
  stack : List Frame
  inv : Inv start visited stack

noncomputable def Search.measure {start : State} (σ : Search start) : Nat :=
  2 * (stateBound - σ.visited.size) + σ.stack.length

/-- A checked answer: each constructor carries the proof that its evidence passes the checker. -/
inductive Outcome (start : State) where
  | win (path : List Move) (h : checkWin start path = true)
  | lose (closed : HashSet State) (h : checkClosed start closed = true)

def Outcome.isWin {start : State} : Outcome start → Bool
  | .win .. => true
  | .lose .. => false

theorem Outcome.isWin_iff {start : State} (o : Outcome start) :
    o.isWin = true ↔ ∃ t, Reachable start t ∧ t.Won := by
  cases o with
  | win p h => simp only [isWin, true_iff]; exact checkWin_sound h
  | lose c h => simp only [isWin, Bool.false_eq_true, false_iff]; exact not_winnable_of_checkClosed h

/-! ## Expanding one position -/

/-- Visit the successors `ps` of the position reached by reversed path `p`. Stops with a
winning reversed path as soon as a won successor appears. -/
def expand (p : List Move) :
    List (Move × State) → HashSet State → List Frame → Except (List Move) (HashSet State × List Frame)
  | [], V, S => .ok (V, S)
  | (m, t) :: rest, V, S =>
    if V.contains t then expand p rest V S
    else if t.won then .error (m :: p)
    else expand p rest (V.insert t) (⟨t, m :: p⟩ :: S)

/-- The invariant while the popped position `s` is being expanded. -/
structure ExpInv (start s : State) (V : HashSet State) (S : List Frame) : Prop where
  start_mem : start ∈ V
  reach : ∀ x, x ∈ V → Reachable start x
  nowin : ∀ x, x ∈ V → x.won = false
  stack_ok : ∀ f ∈ S, f.state ∈ V ∧ replay start f.path.reverse = some f.state
  closed : ∀ x, x ∈ V → (∃ f ∈ S, f.state = x) ∨ (∀ t ∈ moves x, t ∈ V) ∨ x = s

theorem expand_error {start s : State} {p q : List Move} (hp : replay start p.reverse = some s) :
    ∀ {ps : List (Move × State)} {V : HashSet State} {S : List Frame},
      (∀ x ∈ ps, Legal s x.1 x.2) → expand p ps V S = .error q → checkWin start q.reverse = true
  | [], _, _, _, h => by simp [expand] at h
  | (m, t) :: rest, V, S, hl, h => by
    simp only [expand] at h
    split at h
    · exact expand_error hp (fun x hx => hl x (by simp [hx])) h
    · split at h
      · rename_i hw
        simp only [Except.error.injEq] at h; subst h
        have hm : Legal s m t := hl (m, t) (by simp)
        simp only [checkWin, List.reverse_cons, replay_snoc hp, applyMove_eq_some_iff.mpr hm, hw]
      · exact expand_error hp (fun x hx => hl x (by simp [hx])) h

theorem expand_ok {start s : State} {p : List Move} (hp : replay start p.reverse = some s) :
    ∀ {ps : List (Move × State)} {V V' : HashSet State} {S S' : List Frame},
      (∀ x ∈ ps, Legal s x.1 x.2) → ExpInv start s V S → expand p ps V S = .ok (V', S') →
      ExpInv start s V' S' ∧ (∀ x ∈ ps, x.2 ∈ V') ∧ V'.size + S.length = V.size + S'.length ∧
        V.size ≤ V'.size
  | [], V, V', S, S', _, hJ, h => by
    simp only [expand, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨hJ, by simp, rfl, Nat.le_refl _⟩
  | (m, t) :: rest, V, V', S, S', hl, hJ, h => by
    have hl' : ∀ x ∈ rest, Legal s x.1 x.2 := fun x hx => hl x (by simp [hx])
    have hm : Legal s m t := hl (m, t) (by simp)
    simp only [expand] at h
    split at h
    · rename_i hc
      obtain ⟨hJ', hall, hsz, hle⟩ := expand_ok hp hl' hJ h
      refine ⟨hJ', ?_, hsz, hle⟩
      intro x hx
      simp only [List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact expand_ok_mono hp hl' h t (HashSet.mem_iff_contains.mpr hc)
      · exact hall x hx
    · split at h
      · cases h
      · rename_i hc hw
        have hnot : t ∉ V := fun h' => hc (HashSet.mem_iff_contains.mp h')
        have hreach_t : Reachable start t := .tail (reachable_of_replay hp) ⟨m, hm⟩
        have hJ1 : ExpInv start s (V.insert t) (⟨t, m :: p⟩ :: S) := by
          refine ⟨HashSet.mem_insert.mpr (Or.inr hJ.start_mem), ?_, ?_, ?_, ?_⟩
          · intro x hx
            rcases HashSet.mem_insert.mp hx with h' | h'
            · rw [beq_iff_eq] at h'; subst h'; exact hreach_t
            · exact hJ.reach x h'
          · intro x hx
            rcases HashSet.mem_insert.mp hx with h' | h'
            · rw [beq_iff_eq] at h'; subst h'; simpa using hw
            · exact hJ.nowin x h'
          · intro f hf
            simp only [List.mem_cons] at hf
            rcases hf with rfl | hf
            · refine ⟨HashSet.mem_insert_self, ?_⟩
              simp only [List.reverse_cons, replay_snoc hp]
              exact applyMove_eq_some_iff.mpr hm
            · exact ⟨HashSet.mem_insert.mpr (Or.inr (hJ.stack_ok f hf).1), (hJ.stack_ok f hf).2⟩
          · intro x hx
            rcases HashSet.mem_insert.mp hx with h' | h'
            · rw [beq_iff_eq] at h'; subst h'; exact Or.inl ⟨_, List.mem_cons_self .., rfl⟩
            · rcases hJ.closed x h' with ⟨f, hf, hfx⟩ | hx2 | hx2
              · exact Or.inl ⟨f, List.mem_cons_of_mem _ hf, hfx⟩
              · exact Or.inr (Or.inl fun u hu => HashSet.mem_insert.mpr (Or.inr (hx2 u hu)))
              · exact Or.inr (Or.inr hx2)
        obtain ⟨hJ', hall, hsz, hle⟩ := expand_ok hp hl' hJ1 h
        have hsize : (V.insert t).size = V.size + 1 := by
          rw [HashSet.size_insert]; simp [hnot]
        refine ⟨hJ', ?_, by simp only [List.length_cons] at hsz; omega, by omega⟩
        intro x hx
        simp only [List.mem_cons] at hx
        rcases hx with rfl | hx
        · exact expand_ok_mono hp hl' h t HashSet.mem_insert_self
        · exact hall x hx
where
  /-- Visited sets only grow during expansion. -/
  expand_ok_mono {start s : State} {p : List Move} (_hp : replay start p.reverse = some s) :
      ∀ {ps : List (Move × State)} {V V' : HashSet State} {S S' : List Frame},
        (∀ x ∈ ps, Legal s x.1 x.2) → expand p ps V S = .ok (V', S') → ∀ x, x ∈ V → x ∈ V'
    | [], V, V', S, S', _, h => by
      simp only [expand, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h; exact fun _ hx => hx
    | (m, t) :: rest, V, V', S, S', hl, h => by
      have hl' : ∀ x ∈ rest, Legal s x.1 x.2 := fun x hx => hl x (by simp [hx])
      simp only [expand] at h
      split at h
      · exact expand_ok_mono _hp hl' h
      · split at h
        · cases h
        · intro x hx
          exact expand_ok_mono _hp hl' h x (HashSet.mem_insert.mpr (Or.inr hx))

/-! ## The bound on visited positions -/

theorem size_le_stateBound {start : State} (hv : start.Valid) {V : HashSet State}
    (hr : ∀ s, s ∈ V → Reachable start s) : V.size ≤ stateBound := by
  rw [← HashSet.length_toList]
  apply length_le_stateBound
  · exact HashSet.distinct_toList.imp fun h e => by subst e; simp at h
  · intro s hs; exact (hr s (HashSet.mem_toList.mp hs)).valid hv

/-! ## One search step -/

theorem checkClosed_of_inv {start : State} {V : HashSet State} (h : Inv start V []) :
    checkClosed start V = true := by
  have hall : ∀ s ∈ V.toList, (!s.won && (moves s).all V.contains) = true := by
    intro s hs
    have hs' := HashSet.mem_toList.mp hs
    rw [Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true]
    refine ⟨h.nowin s hs', fun t ht => ?_⟩
    rcases h.closed s hs' with ⟨f, hf, _⟩ | hc
    · simp at hf
    · exact HashSet.mem_iff_contains.mp (hc t ht)
  simp only [checkClosed, Bool.and_eq_true]
  exact ⟨HashSet.mem_iff_contains.mp h.start_mem, List.all_eq_true.mpr hall⟩

/-- Pop one pending position and visit its successors. -/
def step {start : State} (hv : start.Valid) (σ : Search start) :
    Outcome start ⊕ { σ' : Search start // σ'.measure < σ.measure } :=
  match hS : σ.stack with
  | [] => .inl (.lose σ.visited (checkClosed_of_inv (hS ▸ σ.inv)))
  | f :: rest =>
    have hf := σ.inv.stack_ok f (by simp [hS])
    -- successors are pushed in heuristic order, so the best-scoring one is explored first
    have hl : ∀ x ∈ orderedSuccs f.state, Legal f.state x.1 x.2 :=
      fun x hx => mem_succs_iff.mp (mem_orderedSuccs.mp hx)
    match he : expand f.path (orderedSuccs f.state) σ.visited rest with
    | .error q => .inl (.win q.reverse (expand_error hf.2 hl he))
    | .ok (V', S') =>
      have hJ : ExpInv start f.state σ.visited rest := by
        refine ⟨σ.inv.start_mem, σ.inv.reach, σ.inv.nowin,
          fun g hg => σ.inv.stack_ok g (by simp [hS, hg]), fun x hx => ?_⟩
        rcases σ.inv.closed x hx with ⟨g, hg, hgx⟩ | hc
        · rw [hS] at hg
          simp only [List.mem_cons] at hg
          rcases hg with rfl | hg
          · exact Or.inr (Or.inr hgx.symm)
          · exact Or.inl ⟨g, hg, hgx⟩
        · exact Or.inr (Or.inl hc)
      have hres := expand_ok hf.2 hl hJ he
      have hinv : Inv start V' S' := by
        obtain ⟨hJ', hall, -, -⟩ := hres
        refine ⟨hJ'.start_mem, hJ'.reach, hJ'.nowin, hJ'.stack_ok, fun x hx => ?_⟩
        rcases hJ'.closed x hx with h1 | h2 | rfl
        · exact Or.inl h1
        · exact Or.inr h2
        · refine Or.inr fun t ht => ?_
          simp only [moves, List.mem_map] at ht
          obtain ⟨y, hy, rfl⟩ := ht
          exact hall y (mem_orderedSuccs.mpr hy)
      .inr ⟨⟨V', S', hinv⟩, by
        obtain ⟨-, -, hsz, hle⟩ := hres
        have hb := size_le_stateBound hv hinv.reach
        simp only [Search.measure, hS, List.length_cons]
        omega⟩

/-! ## The total decision procedure -/

def initSearch (start : State) : Outcome start ⊕ Search start :=
  if hw : start.won = true then .inl (.win [] (by simp [checkWin, replay, hw]))
  else
    let V := (HashSet.emptyWithCapacity 1024 : HashSet State).insert start
    .inr ⟨V, [⟨start, []⟩], by
      have hmem : ∀ x, x ∈ V ↔ x = start := by
        intro x
        simp only [V, HashSet.mem_insert, HashSet.not_mem_emptyWithCapacity, or_false, beq_iff_eq]
        exact eq_comm
      refine ⟨(hmem _).mpr rfl, fun x hx => ?_, fun x hx => ?_, fun f hf => ?_, fun x hx => ?_⟩
      · rw [(hmem x).mp hx]; exact .refl
      · rw [(hmem x).mp hx]; simpa using hw
      · simp only [List.mem_singleton] at hf; subst hf; exact ⟨(hmem _).mpr rfl, rfl⟩
      · rw [(hmem x).mp hx]; exact Or.inl ⟨_, List.mem_singleton_self _, rfl⟩⟩

/-- Run the search to completion. -/
def run {start : State} (hv : start.Valid) (σ : Search start) : Outcome start :=
  match step hv σ with
  | .inl o => o
  | .inr ⟨σ', _⟩ => run hv σ'
termination_by σ.measure

/-- **The reference solver**: total on valid positions, returning checked evidence. -/
def solve (start : State) (hv : start.Valid) : Outcome start :=
  match initSearch start with
  | .inl o => o
  | .inr σ => run hv σ

/-- The decision procedure. -/
def winnable (start : State) (hv : start.Valid) : Bool := (solve start hv).isWin

/-- **Soundness and completeness.** On every valid position the decision procedure returns
`true` exactly when a won position is reachable. Termination is by construction: `solve` is
defined by well-founded recursion on `Search.measure`. -/
theorem winnable_iff (start : State) (hv : start.Valid) :
    winnable start hv = true ↔ ∃ t, Reachable start t ∧ t.Won :=
  (solve start hv).isWin_iff

/-! ## Bounded execution of the same steps -/

/-- Run at most `n` steps of the reference search. -/
def runSteps {start : State} (hv : start.Valid) : Nat → Search start → Outcome start ⊕ Search start
  | 0, σ => .inr σ
  | n + 1, σ =>
    match step hv σ with
    | .inl o => .inl o
    | .inr ⟨σ', _⟩ => runSteps hv n σ'

/-- Fuel derived from the algorithm: `σ.measure + 1` steps always suffice, and the bounded
run then agrees with the reference run. -/
theorem runSteps_eq_run {start : State} (hv : start.Valid) :
    ∀ (n : Nat) (σ : Search start), σ.measure < n → runSteps hv n σ = .inl (run hv σ)
  | 0, _, h => absurd h (Nat.not_lt_zero _)
  | n + 1, σ, h => by
    rw [run]
    simp only [runSteps]
    split
    · rfl
    · rename_i σ' hσ' _
      exact runSteps_eq_run hv n σ' (by omega)

end FreeCell

import FreeCell.Valid

/-!
# Reachability and paths
-/

namespace FreeCell

/-- `Reachable start t`: some sequence of legal single-card moves leads from `start` to `t`. -/
inductive Reachable (start : State) : State → Prop
  | refl : Reachable start start
  | tail {s t : State} : Reachable start s → Step s t → Reachable start t

theorem Reachable.valid {start s : State} (hv : start.Valid) (h : Reachable start s) : s.Valid := by
  induction h with
  | refl => exact hv
  | tail _ hst ih => exact hst.valid ih

/-- Apply moves in order; `none` as soon as one is illegal. -/
def replay (s : State) : List Move → Option State
  | [] => some s
  | m :: ms => (applyMove s m).bind fun t => replay t ms

theorem replay_append {s : State} {ms ms' : List Move} :
    replay s (ms ++ ms') = (replay s ms).bind fun t => replay t ms' := by
  induction ms generalizing s with
  | nil => simp [replay]
  | cons m ms ih =>
    simp only [List.cons_append, replay]
    cases applyMove s m <;> simp [ih]

theorem replay_snoc {s t : State} {ms : List Move} {m : Move} (h : replay s ms = some t) :
    replay s (ms ++ [m]) = applyMove t m := by
  rw [replay_append, h]; simp only [Option.bind_some, replay]; cases applyMove t m <;> rfl

theorem reachable_of_replay' {start s t : State} {ms : List Move} (hs : Reachable start s)
    (h : replay s ms = some t) : Reachable start t := by
  induction ms generalizing s with
  | nil => simp [replay] at h; subst h; exact hs
  | cons m ms ih =>
    simp only [replay, Option.bind_eq_some_iff] at h
    obtain ⟨u, hu, hu'⟩ := h
    exact ih (.tail hs ⟨m, applyMove_eq_some_iff.mp hu⟩) hu'

theorem reachable_of_replay {start t : State} {ms : List Move} (h : replay start ms = some t) :
    Reachable start t :=
  reachable_of_replay' .refl h

/-- Every reachable position is reached by some replayable move list. -/
theorem exists_replay_of_reachable {start t : State} (h : Reachable start t) :
    ∃ ms, replay start ms = some t := by
  induction h with
  | refl => exact ⟨[], rfl⟩
  | tail _ hst ih =>
    obtain ⟨ms, hms⟩ := ih
    obtain ⟨m, hm⟩ := hst
    exact ⟨ms ++ [m], by rw [replay_snoc hms]; exact applyMove_eq_some_iff.mpr hm⟩

end FreeCell

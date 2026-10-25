import FreeCell.Reach
import Std.Data.HashSet

/-!
# Checked evidence for both outcomes

* `checkWin start ms`: replaying `ms` from `start` ends in a won position.
* `checkClosed start c`: `c` contains `start`, holds no won position, and is
  closed under every legal move — the generalisation of the #11982 certificate.

Neither checker assumes anything about how its evidence was produced, nor that
`start` or the certificate's positions are valid.
-/

namespace FreeCell

open Std

def checkWin (start : State) (ms : List Move) : Bool :=
  match replay start ms with
  | some t => t.won
  | none => false

theorem checkWin_sound {start : State} {ms : List Move} (h : checkWin start ms = true) :
    ∃ t, Reachable start t ∧ t.Won := by
  unfold checkWin at h
  split at h
  · rename_i t ht
    exact ⟨t, reachable_of_replay ht, State.won_iff.mp h⟩
  · simp at h

def checkClosed (start : State) (c : HashSet State) : Bool :=
  c.contains start && c.toList.all fun s => !s.won && (moves s).all c.contains

/-- **Unwinnability certificate soundness** (generalises `cert_sound` of #11982). -/
theorem checkClosed_sound {start : State} {c : HashSet State} (h : checkClosed start c = true) :
    ∀ t, Reachable start t → t ∈ c ∧ ¬ t.Won := by
  simp only [checkClosed, Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true',
    HashSet.mem_toList] at h
  obtain ⟨hstart, hall⟩ := h
  have key : ∀ s, s ∈ c → s.won = false ∧ ∀ t ∈ moves s, t ∈ c := by
    intro s hs
    have := hall s hs
    exact ⟨this.1, fun t ht => HashSet.mem_iff_contains.mpr (this.2 t ht)⟩
  have hs0 : start ∈ c := HashSet.mem_iff_contains.mpr hstart
  have notWon : ∀ s, s ∈ c → ¬ s.Won := fun s hs hw =>
    by have := (key s hs).1; rw [← State.won_iff] at hw; simp [hw] at this
  intro t hr
  induction hr with
  | refl => exact ⟨hs0, notWon _ hs0⟩
  | tail _ hst ih =>
    have hc := (key _ ih.1).2 _ (mem_moves_iff.mpr hst)
    exact ⟨hc, notWon _ hc⟩

theorem not_winnable_of_checkClosed {start : State} {c : HashSet State}
    (h : checkClosed start c = true) : ¬ ∃ t, Reachable start t ∧ t.Won :=
  fun ⟨t, hr, hw⟩ => (checkClosed_sound h t hr).2 hw

end FreeCell

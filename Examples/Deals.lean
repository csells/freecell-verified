import FreeCell

/-!
# Corollaries for particular deals

Each result is an instance of `winnable_iff`, with the solver's Boolean answer
evaluated by `native_decide`. That evaluation trusts Lean's compiler (it adds a
`…_native.native_decide…` axiom); the general theorems do not.
-/

namespace FreeCell.Examples

theorem deal11982_unwinnable : ¬ ∃ t, Reachable (msDeal 11982) t ∧ t.Won :=
  fun h => absurd ((winnable_iff _ (msDeal_valid 11982)).mpr h) (by native_decide)

theorem deal1_winnable : ∃ t, Reachable (msDeal 1) t ∧ t.Won :=
  (winnable_iff _ (msDeal_valid 1)).mp (by native_decide)

theorem deal1941_winnable : ∃ t, Reachable (msDeal 1941) t ∧ t.Won :=
  (winnable_iff _ (msDeal_valid 1941)).mp (by native_decide)

end FreeCell.Examples

#print axioms FreeCell.Examples.deal11982_unwinnable
#print axioms FreeCell.Examples.deal1_winnable

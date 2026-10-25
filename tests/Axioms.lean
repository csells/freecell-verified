import FreeCell

/-! Prints the axioms behind each headline theorem. Run: `lake env lean tests/Axioms.lean`. -/

open FreeCell

#check @mem_moves_iff
#check @Legal.valid
#check @length_le_stateBound
#check @msDeal_valid
#check @checkWin_sound
#check @checkClosed_sound
#check @winnable_iff
#check @runSteps_eq_run
#check @verifyCertificate_winnable
#check @verifyCertificate_unwinnable

#print axioms mem_succs_iff
#print axioms mem_moves_iff
#print axioms Legal.valid
#print axioms Reachable.valid
#print axioms length_le_stateBound
#print axioms msDeal_valid
#print axioms checkWin_sound
#print axioms checkClosed_sound
#print axioms solve
#print axioms winnable_iff
#print axioms runSteps_eq_run
#print axioms verifyCertificate_winnable
#print axioms verifyCertificate_unwinnable

#check @Supermove.reachable
#check @superReachable_iff
#print axioms Supermove.reachable
#print axioms superReachable_iff

#check @SafeStep.winsIn
#check @SafeStep.winnable
#check @autoWinnable_iff
#check @autoWinnable_autoPlay_iff
#print axioms SafeStep.winsIn
#print axioms SafeStep.winnable
#print axioms SafeStep.winnable_iff
#print axioms autoWinnable_iff
#print axioms autoWinnable_autoPlay_iff

/- This comment mentions sorry, axiom, native_decide, partial and unsafe;
   /- nested: implemented_by, extern, csimp -/ still a comment. -/
-- a line comment about decide +native and set_option
def msg : String := "sorry, the axiom is partial and unsafe"
def c : Char := 'p'
theorem ok : 2 + 2 = 4 := by decide
def partialSum (xs : List Nat) : Nat := xs.foldl (· + ·) 0

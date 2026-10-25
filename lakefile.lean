import Lake
open Lake DSL

package «freecell-verified» where
  leanOptions := #[⟨`autoImplicit, false⟩]

@[default_target]
lean_lib FreeCell

lean_lib Examples where
  globs := #[.submodules `Examples]

lean_lib FreeCellTest where
  globs := #[.submodules `FreeCellTest]

lean_exe tests where
  root := `FreeCellTest.Main

@[default_target]
lean_exe freecell where
  root := `Main

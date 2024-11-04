import Lake

open Lake DSL

package batteries where
  testDriver := "BatteriesTest"
  lintDriver := "runLinter"

/-!
## Batteries libraries
-/

@[default_target]
lean_lib Batteries where
  leanOptions := #[⟨`linter.missingDocs,true⟩]

lean_lib BatteriesTest where
  globs := #[.submodules `BatteriesTest]

/-!
## Executables provided by Batteries
-/

@[default_target]
lean_exe runLinter where
  srcDir := "scripts"
  supportInterpreter := true

/--
this enables `lake exe test` in downstream projects;
let's not disable that without deprications first.
-/
lean_exe test where
  srcDir := "scripts"

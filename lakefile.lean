import Lake

open Lake DSL

package batteries where
  leanOptions := #[⟨`linter.missingDocs,true⟩]
  testDriver := "test"
  lintDriver := "runLinter"

/-!
## Batteries libraries
-/

@[default_target]
lean_lib Batteries where

/-!
## Executables provided by Batteries
-/

@[default_target]
lean_exe runLinter where
  srcDir := "scripts"
  supportInterpreter := true

lean_exe test where
  srcDir := "scripts"

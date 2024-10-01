import Lake

open Lake DSL

package batteries where
  leanOptions := #[⟨`linter.missingDocs, true⟩]

@[default_target]
lean_lib Batteries

@[default_target, lint_driver]
lean_exe runLinter where
  srcDir := "scripts"
  supportInterpreter := true

@[test_driver]
lean_exe test where
  srcDir := "scripts"

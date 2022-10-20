import Lake

open Lake DSL

package std where
  moreLeanArgs := #["-DwarningAsError=true", "-Dlinter.missingDocs=true"]
  moreServerArgs := #["-Dlinter.missingDocs=true"]

@[default_target]
lean_lib Std

@[default_target]
lean_exe runLinter where
  root := `scripts.runLinter
  supportInterpreter := true

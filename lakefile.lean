import Lake

open Lake DSL

package std where
  moreLeanArgs := #["-DwarningAsError=true", "-Dlinter.missingDocs=true"]
  moreServerArgs := #["-Dlinter.missingDocs=true"]

@[defaultTarget]
lean_lib Std

@[defaultTarget]
lean_exe runLinter where
  root := `scripts.runLinter
  supportInterpreter := true

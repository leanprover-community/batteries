import Lake

open Lake DSL

package std

@[defaultTarget]
lean_lib Std

@[defaultTarget]
lean_exe runLinter where
  root := `scripts.runLinter
  supportInterpreter := true

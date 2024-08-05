import Lake

open Lake DSL

macro "opt_arg?" x:ident v:term : term => `(if get_config? $x |>.isSome then $v else default)

package batteries where
  moreLeanArgs := opt_arg? werror #["-DwarningAsError=true"]
  leanOptions :=
    #[⟨`linter.missingDocs, true⟩] ++
    opt_arg? disable_new_compiler #[⟨`compiler.enableNew, false⟩]

@[default_target]
lean_lib Batteries

@[default_target, lint_driver]
lean_exe runLinter where
  srcDir := "scripts"
  supportInterpreter := true

@[test_driver]
lean_exe test where
  srcDir := "scripts"

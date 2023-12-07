import Lake

open Lake DSL

macro "opt_arg?" x:ident v:term : term =>
  `(if get_config? $x |>.isSome then $v else default)

package std where
  moreLeanArgs := opt_arg? werror #["-DwarningAsError=true"]
  leanOptions :=
    #[⟨`linter.missingDocs, true⟩] ++
    opt_arg? disable_new_compiler #[⟨`compiler.enableNew, false⟩]

@[default_target]
lean_lib Std

@[default_target]
lean_exe runLinter where
  srcDir := "scripts"
  supportInterpreter := true

meta if get_config? doc |>.isSome then
require «doc-gen4» from git "https://github.com/leanprover/doc-gen4" @ "main"

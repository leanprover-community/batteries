import Lake

open Lake DSL

package std where
  moreLeanArgs := #["-DwarningAsError=true"]
  leanOptions := Id.run do
    let mut opts := #[⟨`linter.missingDocs, true⟩]
    if get_config? disable_new_compiler |>.isSome then
      opts := opts.push ⟨`compiler.enableNew, false⟩
    opts

@[default_target]
lean_lib Std

@[default_target]
lean_exe runLinter where
  srcDir := "scripts"
  supportInterpreter := true

meta if get_config? doc = some "on" then
require «doc-gen4» from git "https://github.com/leanprover/doc-gen4" @ "main"

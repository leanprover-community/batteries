import Lake

open Lake DSL

package std := Id.run do
  let mut moreServerArgs := #["-Dlinter.missingDocs=true"]
  if get_config? disable_new_compiler |>.isSome then
    moreServerArgs := moreServerArgs.push "-Dcompiler.enableNew=false"
  let moreLeanArgs := moreServerArgs.push "-DwarningAsError=true"
  pure { name := `std, moreLeanArgs, moreServerArgs }

@[default_target]
lean_lib Std

@[default_target]
lean_exe runLinter where
  root := `scripts.runLinter
  supportInterpreter := true

meta if get_config? doc = some "on" then
require «doc-gen4» from git "https://github.com/leanprover/doc-gen4" @ "main"

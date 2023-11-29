import Lake

open Lake DSL

package std where
  moreLeanArgs := moreServerOptions.map (·.asCliArg) |>.push "-DwarningAsError=true"
  moreServerOptions := moreServerOptions
where
  moreServerOptions := Id.run do
    let mut moreServerOptions := #[⟨`linter.missingDocs, true⟩]
    if get_config? disable_new_compiler |>.isSome then
      moreServerOptions := moreServerOptions.push ⟨`compiler.enableNew, false⟩
    moreServerOptions

@[default_target]
lean_lib Std

@[default_target]
lean_exe runLinter where
  srcDir := "scripts"
  supportInterpreter := true

meta if get_config? doc = some "on" then
require «doc-gen4» from git "https://github.com/leanprover/doc-gen4" @ "main"

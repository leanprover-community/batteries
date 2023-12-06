import Lake

open Lake DSL

/-- Turn a config option into a Boolean -/
def enabled (val : Option String) (default : Bool := false) : Bool :=
  match val with
  | .some "off" => false
  | .some "false" => false
  | .some "on" => true
  | .some "true" => true
  | .some _ => not default -- This allows -K=opt to flip the default.
  | _ => default

-- Selectively choose an option if feature is enabled.
macro "optArg?" x:ident ws d:ident v:term : term =>
  `(if enabled (get_config? $x) $d then $v else default)

package std where
  moreLeanArgs :=
    optArg? werror false #["-DwarningAsError=true"]
  leanOptions :=
    #[⟨`linter.missingDocs, true⟩] ++
    optArg? disable_new_compiler true #[⟨`compiler.enableNew, false⟩]

@[default_target]
lean_lib Std

@[default_target]
lean_exe runLinter where
  srcDir := "scripts"
  supportInterpreter := true

meta if enabled (get_config? doc) then
require «doc-gen4» from git "https://github.com/leanprover/doc-gen4" @ "main"

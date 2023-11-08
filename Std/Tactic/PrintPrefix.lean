/-
Copyright (c) 2021 Shing Tak Lam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shing Tak Lam, Daniel Selsam, Mario Carneiro
-/
import Std.Lean.Util.EnvSearch
import Lean.Elab.Tactic.Config

namespace Lean.Elab.Command

private def appendMatchingConstants (msg : String)
    (ϕ : ConstantInfo → MetaM Bool) (opts : EnvironmentSearchOptions) : MetaM String := do
  let cinfos ← getMatchingConstants ϕ opts
  let cinfos := cinfos.qsort fun p q => p.name.lt q.name
  let mut msg := msg
  for cinfo in cinfos do
    msg := msg ++ s!"{cinfo.name} : {← Meta.ppExpr cinfo.type}\n"
  pure msg

/-- Function elaborating `Config`. -/
declare_config_elab elabEnvironmentSearchOptions EnvironmentSearchOptions

/--
Command for #print prefix
-/
syntax (name := printPrefix) "#print prefix " (Lean.Parser.Tactic.config)? ident : command

/--
The command `#print prefix foo` will print all definitions that start with
the namespace `foo`.
-/
@[command_elab printPrefix] def elabPrintPrefix : CommandElab
| `(#print prefix%$tk $[$cfg:config]? $name:ident) => do
  let nameId := name.getId
  liftTermElabM do
    let opts ← elabEnvironmentSearchOptions (mkOptionalNode cfg)
    let mut msg ← appendMatchingConstants "" (opts:=opts) fun cinfo => pure $ nameId.isPrefixOf cinfo.name
    if msg.isEmpty then
      if let [name] ← resolveGlobalConst name then
        msg ← appendMatchingConstants msg (opts:=opts) fun cinfo => pure $ name.isPrefixOf cinfo.name
    if !msg.isEmpty then
      logInfoAt tk msg
| _ => throwUnsupportedSyntax

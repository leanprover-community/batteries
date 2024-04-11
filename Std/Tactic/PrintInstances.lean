/-
Copyright (c) 2024 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Std.Lean.Name
import Std.Lean.Util.EnvSearch
import Lean.Elab.Tactic.Config

namespace Std.Tactic
open Lean Elab Command Meta

/--
Options to control `#print instances` command.
-/
structure PrintInstancesConfig where

/-- Function elaborating `Config`. -/
declare_config_elab elabPrintInstancesConfig PrintInstancesConfig

/--
The command `#print instances foo` will print all definitions that would unify with `foo`
as the first step in an instance synthesis (see `#synth`). Unlike `#synth`, it allows `_`
placeholders and will show all matching instances, not just the highest priority instance.

For example, the command below will print out all registered `Monad` instances in the environment:

```lean
#print instances Monad _
```
-/
elab (name := printInstances) "#print" tk:&"instances"
    cfg:(Lean.Parser.Tactic.config)? type:term : command =>
  withoutModifyingEnv <| runTermElabM fun _ => Term.withDeclName `_print_instances_cmd do
    let {} ← elabPrintInstancesConfig (mkOptionalNode cfg)
    let type ← Term.elabTerm type none
    Term.synthesizeSyntheticMVarsNoPostponing
    show MetaM _ from do
    let (args, _, _) ← forallMetaTelescope (← inferType type)
    let type ← instantiateMVars (mkAppN type args)
    unless ← isType type do throwError "expected a type, got{indentExpr type}"
    let mvar ← mkFreshExprMVar type
    let insts ← (← SynthInstance.getInstances type).filterM fun inst => do
      let s ← saveState
      try
        pure (← SynthInstance.tryResolve mvar inst).isSome
      finally
        restoreState s
    let mut msg := m!""
    for inst in insts.reverse do
      if let .const c .. := inst.val.getAppFn then
        msg := msg ++ .ofPPFormat { pp := fun
          | some ctx => ctx.runMetaM <|
            withOptions (pp.tagAppFns.set · true) <| PrettyPrinter.ppSignature c
          | none     => return f!"{c}"  -- should never happen
        } ++ "\n"
      else
        msg := msg ++ m!"{inst.val} : {← inferType inst.val}\n"
    if !msg.isEmpty then
      logInfoAt tk msg

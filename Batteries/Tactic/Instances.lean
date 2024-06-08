/-
Copyright (c) 2023 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
import Lean.Elab.Command
import Lean.PrettyPrinter

/-! # `#instances` command

The `#instances` command prints lists all instances that apply to the given type, if it is a class.
It is similar to `#synth` but it only does the very first step of the instance synthesis algorithm,
which is to enumerate potential instances.
-/

open Lean Elab Command Meta

namespace Batteries.Tactic.Instances

/-- `#instances term` prints all the instances for the given class.
For example, `#instances Add _` gives all `Add` instances, and `#instances Add Nat` gives the
`Nat` instance. The `term` can be any type that can appear in `[...]` binders.

Trailing underscores can be omitted, and `#instances Add` and `#instances Add _` are equivalent;
the command adds metavariables until the argument is no longer a function.

The `#instances` command is closely related to `#synth`, but `#synth` does the full
instance synthesis algorithm and `#instances` does the first step of finding potential instances. -/
elab (name := instancesCmd) tk:"#instances " stx:term : command => runTermElabM fun _ => do
  let type ← Term.elabTerm stx none
  -- Throw in missing arguments using metavariables.
  let (args, _, _) ← withDefault <| forallMetaTelescopeReducing (← inferType type)
  -- Use free variables for explicit quantifiers
  withDefault <| forallTelescopeReducing (mkAppN type args) fun _ type => do
    let some className ← isClass? type
      | throwErrorAt stx "type class instance expected{indentExpr type}"
    let globalInstances ← getGlobalInstancesIndex
    let result ← globalInstances.getUnify type tcDtConfig
    let erasedInstances ← getErasedInstances
    let mut msgs := #[]
    for e in result.insertionSort fun e₁ e₂ => e₁.priority < e₂.priority do
      let Expr.const c _ := e.val | unreachable!
      if erasedInstances.contains c then
        continue
      let mut msg := m!"\n"
      if e.priority != 1000 then -- evalPrio default := 1000
        msg := msg ++ m!"(prio {e.priority}) "
      msgs := msgs.push <| msg ++ MessageData.signature c
    for linst in ← getLocalInstances do
      if linst.className == className then
        msgs := msgs.push m!"(local) {linst.fvar} : {← inferType linst.fvar}"
    if msgs.isEmpty then
      logInfoAt tk m!"No instances"
    else
      let instances := if msgs.size == 1 then "instance" else "instances"
      logInfoAt tk <| msgs.reverse.foldl (·++·) m!"{msgs.size} {instances}:\n"

@[inherit_doc instancesCmd]
macro tk:"#instances" bi:(ppSpace bracketedBinder)* " : " t:term : command =>
  `(command| variable $bi* in #instances%$tk $t)

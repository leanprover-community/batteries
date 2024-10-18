/-
Copyright (c) 2022 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Lean.Elab.Command
import Lean.Util.FoldConsts

open Lean Elab Command

namespace Batteries.Tactic.CollectOpaques

/-- Collects the result of a `CollectOpaques` query. -/
structure State where
  /-- The set visited constants. -/
  visited : NameSet := {}
  /-- The collected opaque defs. -/
  opaques : Array Name := #[]

/-- The monad used by `CollectOpaques`. -/
abbrev M := ReaderT Environment <| StateT State MetaM

/-- Collect the results for a given constant. -/
partial def collect (c : Name) : M Unit := do
  let collectExpr (e : Expr) : M Unit := e.getUsedConstants.forM collect
  let s ← get
  unless s.visited.contains c do
    modify fun s => { s with visited := s.visited.insert c }
    let env ← read
    match env.find? c with
    | some (ConstantInfo.ctorInfo _)
    | some (ConstantInfo.recInfo _)
    | some (ConstantInfo.inductInfo _)
    | some (ConstantInfo.quotInfo _)   =>
      pure ()
    | some (ConstantInfo.defnInfo v)
    | some (ConstantInfo.thmInfo v)    =>
      unless ← Meta.isProp v.type do collectExpr v.value
    | some (ConstantInfo.axiomInfo v)
    | some (ConstantInfo.opaqueInfo v) =>
      unless ← Meta.isProp v.type do
        modify fun s => { s with opaques := s.opaques.push c }
    | none                             =>
      modify fun s => { s with opaques := s.opaques.push c }

end CollectOpaques

/--
The command `#print opaques X` prints all opaque and partial definitions that `X` depends on.

For example, the follwing command prints all opaque and partial definitions that `Classical.choose`
depends on.
```
#print opaques Classical.choose
```
The output is:
```
'Classical.choose' depends on opaque or partial definitions: [Classical.choice]
```

Opaque and partial definitions that occur in a computationally irrelevant context are ignored.
For example,
```
#print opaques Classical.em
```
outputs `'Classical.em' does not use any opaque or partial definitions`. But
```
#print axioms Classical.em
```
reveals that `'Classical.em' depends on axioms: [propext, Classical.choice, Quot.sound]`. The
reason is that `Classical.em` is a `Prop` and it is itself computationally irrelevant.

Axioms are not the only opaque definitions. In fact, the outputs of `#print axioms` and
`#print opaques` are often quite different.
```
#print opaques Std.HashMap.insert
```
show that `'Std.HashMap.insert' depends on opaque or partial definitions:
[System.Platform.getNumBits, UInt64.toUSize]`. But
```
#print axioms Std.HashMap.insert
```
gives `'Std.HashMap.insert' depends on axioms: [propext, Classical.choice, Quot.sound]`. The axioms
`propext` and `Quot.sound` are computationally irrelevant. The axiom `Classical.choice` is
computationally relevant. The reason it does not appear in the list of opaques is that it is only
used inside proofs of propositions, so it is not used in a computationally relevant context.
-/
elab "#print" &"opaques" name:ident : command => do
  let constName ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo name
  let env ← getEnv
  let (_, s) ← liftTermElabM <| ((CollectOpaques.collect constName).run env).run {}
  if s.opaques.isEmpty then
    logInfo m!"'{constName}' does not use any opaque or partial definitions"
  else
    logInfo m!"'{constName}' depends on opaque or partial definitions: {s.opaques.toList}"

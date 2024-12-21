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
      panic! s!"unknown constant {c}"

end CollectOpaques

/--
The command `#print opaques X` prints all opaque definitions that `X` depends on.

Opaque definitions include partial definitions and axioms. Only dependencies that occur in a
computationally relevant context are listed, occurrences within proof terms are omitted. This is
useful to determine whether and how a definition is possibly platform dependent, possibly partial,
or possibly noncomputable.

The command `#print opaques Std.HashMap.insert` shows that `Std.HashMap.insert` depends on the
opaque definitions: `System.Platform.getNumBits` and `UInt64.toUSize`. Thus `Std.HashMap.insert`
may have different behavior when compiled on a 32 bit or 64 bit platform.

The command `#print opaques Stream.forIn` shows that `Stream.forIn` is possibly partial since it
depends on the partial definition `Stream.forIn.visit`. Indeed, `Stream.forIn` may not terminate
when the input stream is unbounded.

The command `#print opaques Classical.choice` shows that `Classical.choice` is itself an opaque
definition: it is an axiom. However, `#print opaques Classical.axiomOfChoice` returns nothing
since it is a proposition, hence not computationally relevant. (The command `#print axioms` does
reveal that `Classical.axiomOfChoice` depends on the `Classical.choice` axiom.)
-/
elab "#print" &"opaques" name:ident : command => do
  let constName ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo name
  let env ← getEnv
  let (_, s) ← liftTermElabM <| ((CollectOpaques.collect constName).run env).run {}
  if s.opaques.isEmpty then
    logInfo m!"'{constName}' does not use any opaque or partial definitions"
  else
    logInfo m!"'{constName}' depends on opaque or partial definitions: {s.opaques.toList}"

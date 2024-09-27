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
The command `#print opaques X` prints all opaque or partial definitions that `X` depends on.

...
-/
elab "#print" &"opaques" name:ident : command => do
  let constName ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo name
  let env ← getEnv
  let (_, s) ← liftTermElabM <| ((CollectOpaques.collect constName).run env).run {}
  if s.opaques.isEmpty then
    logInfo m!"'{constName}' does not use any partial definitions"
  else
    logInfo m!"'{constName}' depends on opaque or partial definitions: {s.opaques.toList}"

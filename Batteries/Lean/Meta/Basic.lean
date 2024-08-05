/-
Copyright (c) 2022 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Jannis Limperg
-/
import Lean.Meta.Tactic.Intro

open Lean Lean.Meta

namespace Lean

/--
Sort the given `FVarId`s by the order in which they appear in the current local
context. If any of the `FVarId`s do not appear in the current local context, the
result is unspecified.
-/
def Meta.sortFVarsByContextOrder [Monad m] [MonadLCtx m]
    (hyps : Array FVarId) : m (Array FVarId) :=
  return (← getLCtx).sortFVarsByContextOrder hyps


namespace MetavarContext

/--
Get the `MetavarDecl` of `mvarId`. If `mvarId` is not a declared metavariable
in the given `MetavarContext`, throw an error.
-/
def getExprMVarDecl [Monad m] [MonadError m] (mctx : MetavarContext)
    (mvarId : MVarId) : m MetavarDecl := do
  if let some mdecl := mctx.decls.find? mvarId then
    return mdecl
  else
    throwError "unknown metavariable '?{mvarId.name}'"

/--
Declare a metavariable. You must make sure that the metavariable is not already
declared.
-/
def declareExprMVar (mctx : MetavarContext) (mvarId : MVarId)
    (mdecl : MetavarDecl) : MetavarContext :=
  { mctx with decls := mctx.decls.insert mvarId mdecl }

/--
Check whether a metavariable is assigned or delayed-assigned. A
delayed-assigned metavariable is already 'solved' but the solution cannot be
substituted yet because we have to wait for some other metavariables to be
assigned first. So in most situations you want to treat a delayed-assigned
metavariable as assigned.
-/
def isExprMVarAssignedOrDelayedAssigned (mctx : MetavarContext)
    (mvarId : MVarId) : Bool :=
  mctx.eAssignment.contains mvarId || mctx.dAssignment.contains mvarId

/--
Check whether a metavariable is declared in the given `MetavarContext`.
-/
def isExprMVarDeclared (mctx : MetavarContext) (mvarId : MVarId) : Bool :=
  mctx.decls.contains mvarId

/--
Erase any assignment or delayed assignment of the given metavariable.
-/
def eraseExprMVarAssignment (mctx : MetavarContext) (mvarId : MVarId) :
    MetavarContext :=
  { mctx with
    eAssignment := mctx.eAssignment.erase mvarId
    dAssignment := mctx.dAssignment.erase mvarId }

/--
Obtain all unassigned metavariables from the given `MetavarContext`. If
`includeDelayed` is `true`, delayed-assigned metavariables are considered
unassigned.
-/
def unassignedExprMVars (mctx : MetavarContext) (includeDelayed := false) :
    Array MVarId := Id.run do
  let mut result := #[]
  for (mvarId, _) in mctx.decls do
    if ! mctx.eAssignment.contains mvarId &&
        (includeDelayed || ! mctx.dAssignment.contains mvarId) then
      result := result.push mvarId
  return result

end MetavarContext


namespace MVarId

/--
Check whether a metavariable is declared.
-/
def isDeclared [Monad m] [MonadMCtx m] (mvarId : MVarId) : m Bool :=
  return (← getMCtx).isExprMVarDeclared mvarId

/--
Erase any assignment or delayed assignment of the given metavariable.
-/
def eraseAssignment [MonadMCtx m] (mvarId : MVarId) : m Unit :=
  modifyMCtx (·.eraseExprMVarAssignment mvarId)

/-- Solve a goal by synthesizing an instance. -/
-- FIXME: probably can just be `g.inferInstance` once leanprover/lean4#2054 is fixed
def synthInstance (g : MVarId) : MetaM Unit := do
  g.assign (← Lean.Meta.synthInstance (← g.getType))

/-- Get the type the given metavariable after instantiating metavariables and cleaning up
annotations. -/
def getTypeCleanup (mvarId : MVarId) : MetaM Expr :=
  return (← instantiateMVars (← mvarId.getType)).cleanupAnnotations

end MVarId


namespace Meta

/--
Obtain all unassigned metavariables. If `includeDelayed` is `true`,
delayed-assigned metavariables are considered unassigned.
-/
def getUnassignedExprMVars [Monad m] [MonadMCtx m] (includeDelayed := false) :
    m (Array MVarId) :=
  return (← getMCtx).unassignedExprMVars (includeDelayed := includeDelayed)

/--
Run a computation with hygiene turned off.
-/
def unhygienic [MonadWithOptions m] (x : m α) : m α :=
  withOptions (tactic.hygienic.set · false) x

/--
A variant of `mkFreshId` which generates names with a particular prefix. The
generated names are unique and have the form `<prefix>.<N>` where `N` is a
natural number. They are not suitable as user-facing names.
-/
def mkFreshIdWithPrefix [Monad m] [MonadNameGenerator m] («prefix» : Name) :
    m Name := do
  let ngen ← getNGen
  let r := { ngen with namePrefix := «prefix» }.curr
  setNGen ngen.next
  pure r

/--
`saturate1 goal tac` runs `tac` on `goal`, then on the resulting goals, etc.,
until `tac` does not apply to any goal any more (i.e. it returns `none`). The
order of applications is depth-first, so if `tac` generates goals `[g₁, g₂, ⋯]`,
we apply `tac` to `g₁` and recursively to all its subgoals before visiting `g₂`.
If `tac` does not apply to `goal`, `saturate1` returns `none`. Otherwise it
returns the generated subgoals to which `tac` did not apply. `saturate1`
respects the `MonadRecDepth` recursion limit.
-/
partial def saturate1 [Monad m] [MonadError m] [MonadRecDepth m] [MonadLiftT (ST IO.RealWorld) m]
    (goal : MVarId) (tac : MVarId → m (Option (Array MVarId))) : m (Option (Array MVarId)) := do
  let some goals ← tac goal | return none
  let acc ← ST.mkRef #[]
  goals.forM (go acc)
  return some (← acc.get)
where
  /-- Auxiliary definition for `saturate1`. -/
  go (acc : IO.Ref (Array MVarId)) (goal : MVarId) : m Unit :=
    withIncRecDepth do
      match ← tac goal with
      | none => acc.modify fun s => s.push goal
      | some goals => goals.forM (go acc)

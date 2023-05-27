/-
Copyright (c) 2022 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Jannis Limperg
-/
import Lean.Meta

open Lean Lean.Meta

namespace Lean

/--
Set the kind of a `LocalDecl`.
-/
def LocalDecl.setKind : LocalDecl → LocalDeclKind → LocalDecl
  | cdecl index fvarId userName type bi _, kind =>
      cdecl index fvarId userName type bi kind
  | ldecl index fvarId userName type value nonDep _, kind =>
      ldecl index fvarId userName type value nonDep kind


namespace LocalContext

/--
Set the kind of the given fvar.
-/
def setKind (lctx : LocalContext) (fvarId : FVarId)
    (kind : LocalDeclKind) : LocalContext :=
  lctx.modifyLocalDecl fvarId (·.setKind kind)

/--
Sort the given `FVarId`s by the order in which they appear in `lctx`. If any of
the `FVarId`s do not appear in `lctx`, the result is unspecified.
-/
def sortFVarsByContextOrder (lctx : LocalContext) (hyps : Array FVarId) :
    Array FVarId :=
  let hyps := hyps.map λ fvarId =>
    match lctx.fvarIdToDecl.find? fvarId with
    | none => (0, fvarId)
    | some ldecl => (ldecl.index, fvarId)
  hyps.qsort (λ h i => h.fst < i.fst) |>.map (·.snd)

end LocalContext


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
Add a delayed assignment for the given metavariable. You must make sure that
the metavariable is not already assigned or delayed-assigned.
-/
def delayedAssignExprMVar (mctx : MetavarContext) (mvarId : MVarId)
    (ass : DelayedMetavarAssignment) : MetavarContext :=
  { mctx with dAssignment := mctx.dAssignment.insert mvarId ass }

/--
Erase any assignment or delayed assignment of the given metavariable.
-/
def eraseExprMVarAssignment (mctx : MetavarContext) (mvarId : MVarId) :
    MetavarContext :=
  { mctx with
    eAssignment := mctx.eAssignment.erase mvarId
    dAssignment := mctx.dAssignment.erase mvarId }

/--
Modify the declaration of a metavariable. If the metavariable is not declared,
the `MetavarContext` is returned unchanged.

You must ensure that the modification is legal. In particular, expressions may
only be replaced with defeq expressions.
-/
def modifyExprMVarDecl (mctx : MetavarContext) (mvarId : MVarId)
    (f : MetavarDecl → MetavarDecl) : MetavarContext :=
  if let some mdecl := mctx.decls.find? mvarId then
    { mctx with decls := mctx.decls.insert mvarId (f mdecl) }
  else
    mctx

/--
Modify the local context of a metavariable. If the metavariable is not declared,
the `MetavarContext` is returned unchanged.

You must ensure that the modification is legal. In particular, expressions may
only be replaced with defeq expressions.
-/
def modifyExprMVarLCtx (mctx : MetavarContext) (mvarId : MVarId)
    (f : LocalContext → LocalContext) : MetavarContext :=
  mctx.modifyExprMVarDecl mvarId λ mdecl => { mdecl with lctx := f mdecl.lctx }

/--
Set the kind of an fvar. If the given metavariable is not declared or the
given fvar doesn't exist in its context, the `MetavarContext` is returned
unchanged.
-/
def setFVarKind (mctx : MetavarContext) (mvarId : MVarId) (fvarId : FVarId)
    (kind : LocalDeclKind) : MetavarContext :=
  mctx.modifyExprMVarLCtx mvarId (·.setKind fvarId kind)

/--
Set the `BinderInfo` of an fvar. If the given metavariable is not declared or
the given fvar doesn't exist in its context, the `MetavarContext` is returned
unchanged.
-/
def setFVarBinderInfo (mctx : MetavarContext) (mvarId : MVarId)
    (fvarId : FVarId) (bi : BinderInfo) : MetavarContext :=
  mctx.modifyExprMVarLCtx mvarId (·.setBinderInfo fvarId bi)

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
Check whether a metavariable is assigned or delayed-assigned. A
delayed-assigned metavariable is already 'solved' but the solution cannot be
substituted yet because we have to wait for some other metavariables to be
assigned first. So in most situations you want to treat a delayed-assigned
metavariable as assigned.
-/
def isAssignedOrDelayedAssigned [Monad m] [MonadMCtx m] (mvarId : MVarId) :
    m Bool :=
  return (← getMCtx).isExprMVarAssignedOrDelayedAssigned mvarId

/--
Check whether a metavariable is declared.
-/
def isDeclared [Monad m] [MonadMCtx m] (mvarId : MVarId) : m Bool :=
  return (← getMCtx).isExprMVarDeclared mvarId

/--
Add a delayed assignment for the given metavariable. You must make sure that
the metavariable is not already assigned or delayed-assigned.
-/
def delayedAssign [MonadMCtx m] (mvarId : MVarId)
    (ass : DelayedMetavarAssignment) : m Unit :=
  modifyMCtx (·.delayedAssignExprMVar mvarId ass)

/--
Erase any assignment or delayed assignment of the given metavariable.
-/
def eraseAssignment [MonadMCtx m] (mvarId : MVarId) : m Unit :=
  modifyMCtx (·.eraseExprMVarAssignment mvarId)

/--
Modify the declaration of a metavariable. If the metavariable is not declared,
nothing happens.

You must ensure that the modification is legal. In particular, expressions may
only be replaced with defeq expressions.
-/
def modifyDecl [MonadMCtx m] (mvarId : MVarId)
    (f : MetavarDecl → MetavarDecl) : m Unit :=
  modifyMCtx (·.modifyExprMVarDecl mvarId f)

/--
Modify the local context of a metavariable. If the metavariable is not declared,
nothing happens.

You must ensure that the modification is legal. In particular, expressions may
only be replaced with defeq expressions.
-/
def modifyLCtx [MonadMCtx m] (mvarId : MVarId)
    (f : LocalContext → LocalContext) : m Unit :=
  modifyMCtx (·.modifyExprMVarLCtx mvarId f)

/--
Set the kind of an fvar. If the given metavariable is not declared or the
given fvar doesn't exist in its context, nothing happens.
-/
def setFVarKind [MonadMCtx m] (mvarId : MVarId) (fvarId : FVarId)
    (kind : LocalDeclKind) : m Unit :=
  modifyMCtx (·.setFVarKind mvarId fvarId kind)

/--
Set the `BinderInfo` of an fvar. If the given metavariable is not declared or
the given fvar doesn't exist in its context, nothing happens.
-/
def setFVarBinderInfo [MonadMCtx m] (mvarId : MVarId) (fvarId : FVarId)
    (bi : BinderInfo) : m Unit :=
  modifyMCtx (·.setFVarBinderInfo mvarId fvarId bi)

/--
Collect the metavariables which `mvarId` depends on. These are the metavariables
which appear in the type and local context of `mvarId`, as well as the
metavariables which *those* metavariables depend on, etc.
-/
partial def getMVarDependencies (mvarId : MVarId) (includeDelayed := false) :
    MetaM (HashSet MVarId) :=
  (·.snd) <$> (go mvarId).run {}
where
  /-- Auxiliary definition for `getMVarDependencies`. -/
  addMVars (e : Expr) : StateRefT (HashSet MVarId) MetaM Unit := do
    let mvars ← getMVars e
    let mut s ← get
    set ({} : HashSet MVarId) -- Ensure that `s` is not shared.
    for mvarId in mvars do
      if ← pure includeDelayed <||> notM (mvarId.isDelayedAssigned) then
        s := s.insert mvarId
    set s
    mvars.forM go

  /-- Auxiliary definition for `getMVarDependencies`. -/
  go (mvarId : MVarId) : StateRefT (HashSet MVarId) MetaM Unit :=
    withIncRecDepth do
      let mdecl ← mvarId.getDecl
      addMVars mdecl.type
      for ldecl in mdecl.lctx do
        addMVars ldecl.type
        if let (some val) := ldecl.value? then
          addMVars val
      if let (some ass) ← getDelayedMVarAssignment? mvarId then
        let pendingMVarId := ass.mvarIdPending
        if ← notM pendingMVarId.isAssignedOrDelayedAssigned then
          modify (·.insert pendingMVarId)
        go pendingMVarId

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
Implementation of `repeat'` and `repeat1'`.

`repeat'Core f` runs `f` on all of the goals to produce a new list of goals,
then runs `f` again on all of those goals, and repeats until `f` fails on all remaining goals,
or until `maxIters` total calls to `f` have occurred.

Returns a boolean indicating whether `f` succeeded at least once, and
all the remaining goals (i.e. those on which `f` failed).
-/
def repeat'Core [Monad m] [MonadError m] [MonadMCtx m]
    (f : MVarId → m (List MVarId)) (gs : List MVarId) (maxIters := 100000) :
    m (Bool × List MVarId) := do
  let (progress, acc) ← go maxIters false gs [] #[]
  pure (progress, (← acc.filterM fun g => not <$> g.isAssigned).toList)
where
  /-- Auxiliary for `repeat'Core`. `repeat'Core.go f maxIters progress gs stk acc` evaluates to
  essentially `acc.toList ++ repeat' f (gs::stk).join maxIters`: that is, `acc` are goals we will
  not revisit, and `(gs::stk).join` is the accumulated todo list of subgoals. -/
  go : Nat → Bool → List MVarId → List (List MVarId) → Array MVarId → m (Bool × Array MVarId)
  | _, p, [], [], acc => pure (p, acc)
  | n, p, [], gs::stk, acc => go n p gs stk acc
  | n, p, g::gs, stk, acc => do
    if ← g.isAssigned then
      go n p gs stk acc
    else
      match n with
      | 0 => pure <| (p, acc.push g ++ gs |> stk.foldl .appendList)
      | n+1 =>
        match ← observing (f g) with
        | .ok gs' => go n true gs' (gs::stk) acc
        | .error _ => go n p gs stk (acc.push g)
termination_by _ n p gs stk _ => (n, stk, gs)

/--
`repeat' f` runs `f` on all of the goals to produce a new list of goals,
then runs `f` again on all of those goals, and repeats until `f` fails on all remaining goals,
or until `maxIters` total calls to `f` have occurred.
Always succeeds (returning the original goals if `f` fails on all of them).
-/
def repeat' [Monad m] [MonadError m] [MonadMCtx m]
    (f : MVarId → m (List MVarId)) (gs : List MVarId) (maxIters := 100000) : m (List MVarId) :=
  repeat'Core f gs maxIters <&> (·.2)

/--
`repeat1' f` runs `f` on all of the goals to produce a new list of goals,
then runs `f` again on all of those goals, and repeats until `f` fails on all remaining goals,
or until `maxIters` total calls to `f` have occurred.
Fails if `f` does not succeed at least once.
-/
def repeat1' [Monad m] [MonadError m] [MonadMCtx m]
    (f : MVarId → m (List MVarId)) (gs : List MVarId) (maxIters := 100000) : m (List MVarId) := do
  let (.true, gs) ← repeat'Core f gs maxIters | throwError "repeat1' made no progress"
  pure gs

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
      | none => acc.modify λ s => s.push goal
      | some goals => goals.forM (go acc)

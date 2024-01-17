/-
Copyright (c) 2022 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Jannis Limperg
-/
import Lean.Meta
import Std.Lean.LocalContext

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
  mctx.modifyExprMVarDecl mvarId fun mdecl => { mdecl with lctx := f mdecl.lctx }

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

/-- Check if a goal is of a subsingleton type. -/
def isSubsingleton (g : MVarId) : MetaM Bool := do
  try
    discard <| synthInstance (← mkAppM ``Subsingleton #[← g.getType])
    return true
  catch _ =>
    return false

/--
Check if a goal is "independent" of a list of other goals.
We say a goal is independent of other goals if assigning a value to it
can not change the assignability of the other goals.

Examples:
* `?m_1 : Type` is not independent of `?m_2 : ?m_1`,
  because we could assign `true : Bool` to `?m_2`,
  but if we first assign `Nat` to `?m_1` then that is no longer possible.
* `?m_1 : Nat` is not independent of `?m_2 : Fin ?m_1`,
  because we could assign `37 : Fin 42` to `?m_2`,
  but if we first assign `2` to `?m_1` then that is no longer possible.
* `?m_1 : ?m_2` is not independent of `?m_2 : Type`, because we could assign `Bool` to ?m_2`,
  but if we first assign `0 : Nat` to `?m_1` then that is no longer possible.
* Given `P : Prop` and `f : P → Type`, `?m_1 : P` is independent of `?m_2 : f ?m_1`
  by proof irrelevance.
* Similarly given `f : Fin 0 → Type`, `?m_1 : Fin 0` is independent of `?m_2 : f ?m_1`,
  because `Fin 0` is a subsingleton.
* Finally `?m_1 : Nat` is independent of `?m_2 : α`,
  as long as `?m_1` does not appear in `Meta.getMVars α`
  (note that `Meta.getMVars` follows delayed assignments).

This function only calculates a conservative approximation of this condition.
That is, it may return `false` when it should return `true`.
(In particular it returns false whenever the type of `g` contains a metavariable,
regardless of whether this is related to the metavariables in `L`.)
-/
def isIndependentOf (L : List MVarId) (g : MVarId) : MetaM Bool := g.withContext do
  let t ← instantiateMVars (← g.getType)
  if t.hasExprMVar then
    -- If the goal's type contains other meta-variables,
    -- we conservatively say that `g` is not independent.
    -- It would be possible to check if `L` depends on these meta-variables.
    return false
  if (← inferType t).isProp then
    -- If the goal is propositional,
    -- proof-irrelevance ensures it is independent of any other goals.
    return true
  if ← g.isSubsingleton then
    -- If the goal is a subsingleton, it is independent of any other goals.
    return true
  -- Finally, we check if the goal `g` appears in the type of any of the goals `L`.
  L.allM fun g' => do pure !((← getMVarDependencies g').contains g)

/-- Solve a goal by synthesizing an instance. -/
-- FIXME: probably can just be `g.inferInstance` once leanprover/lean4#2054 is fixed
def synthInstance (g : MVarId) : MetaM Unit := do
  g.assign (← Lean.Meta.synthInstance (← g.getType))

/--
Replace hypothesis `hyp` in goal `g` with `proof : typeNew`.
The new hypothesis is given the same user name as the original,
it attempts to avoid reordering hypotheses, and the original is cleared if possible.
-/
-- adapted from Lean.Meta.replaceLocalDeclCore
def replace (g : MVarId) (hyp : FVarId) (proof : Expr) (typeNew : Option Expr := none) :
    MetaM AssertAfterResult :=
  g.withContext do
    let typeNew ← match typeNew with
    | some t => pure t
    | none => inferType proof
    let ldecl ← hyp.getDecl
    -- `typeNew` may contain variables that occur after `hyp`.
    -- Thus, we use the auxiliary function `findMaxFVar` to ensure `typeNew` is well-formed
    -- at the position we are inserting it.
    let (_, ldecl') ← findMaxFVar typeNew |>.run ldecl
    let result ← g.assertAfter ldecl'.fvarId ldecl.userName typeNew proof
    (return { result with mvarId := ← result.mvarId.clear hyp }) <|> pure result
where
  /-- Finds the `LocalDecl` for the FVar in `e` with the highest index. -/
  findMaxFVar (e : Expr) : StateRefT LocalDecl MetaM Unit :=
    e.forEach' fun e => do
      if e.isFVar then
        let ldecl' ← e.fvarId!.getDecl
        modify fun ldecl => if ldecl'.index > ldecl.index then ldecl' else ldecl
        return false
      else
        return e.hasFVar

/-- Add the hypothesis `h : t`, given `v : t`, and return the new `FVarId`. -/
def note (g : MVarId) (h : Name) (v : Expr) (t? : Option Expr := .none) :
    MetaM (FVarId × MVarId) := do
  (← g.assert h (← match t? with | some t => pure t | none => inferType v) v).intro1P

/-- Get the type the given metavariable after instantiating metavariables and cleaning up
annotations. -/
def getTypeCleanup (mvarId : MVarId) : MetaM Expr :=
  return (← instantiateMVars (← mvarId.getType)).cleanupAnnotations

/-- Short-hand for applying a constant to the goal. -/
def applyConst (mvar : MVarId) (c : Name) (cfg : ApplyConfig := {}) : MetaM (List MVarId) := do
  mvar.apply (← mkConstWithFreshMVarLevels c) cfg

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
def repeat'Core [Monad m] [MonadExcept ε m] [MonadBacktrack s m] [MonadMCtx m]
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
        match ← observing? (f g) with
        | some gs' => go n true gs' (gs::stk) acc
        | none => go n p gs stk (acc.push g)
termination_by n p gs stk _ => (n, stk, gs)

/--
`repeat' f` runs `f` on all of the goals to produce a new list of goals,
then runs `f` again on all of those goals, and repeats until `f` fails on all remaining goals,
or until `maxIters` total calls to `f` have occurred.
Always succeeds (returning the original goals if `f` fails on all of them).
-/
def repeat' [Monad m] [MonadExcept ε m] [MonadBacktrack s m] [MonadMCtx m]
    (f : MVarId → m (List MVarId)) (gs : List MVarId) (maxIters := 100000) : m (List MVarId) :=
  repeat'Core f gs maxIters <&> (·.2)

/--
`repeat1' f` runs `f` on all of the goals to produce a new list of goals,
then runs `f` again on all of those goals, and repeats until `f` fails on all remaining goals,
or until `maxIters` total calls to `f` have occurred.
Fails if `f` does not succeed at least once.
-/
def repeat1' [Monad m] [MonadError m] [MonadExcept ε m] [MonadBacktrack s m] [MonadMCtx m]
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
      | none => acc.modify fun s => s.push goal
      | some goals => goals.forM (go acc)

/-- Return local hypotheses which are not "implementation detail", as `Expr`s. -/
def getLocalHyps [Monad m] [MonadLCtx m] : m (Array Expr) := do
  let mut hs := #[]
  for d in ← getLCtx do
    if !d.isImplementationDetail then hs := hs.push d.toExpr
  return hs

/--
Given a monadic function `F` that takes a type and a term of that type and produces a new term,
lifts this to the monadic function that opens a `∀` telescope, applies `F` to the body,
and then builds the lambda telescope term for the new term.
-/
def mapForallTelescope' (F : Expr → Expr → MetaM Expr) (forallTerm : Expr) : MetaM Expr := do
  forallTelescope (← Meta.inferType forallTerm) fun xs ty => do
    Meta.mkLambdaFVars xs (← F ty (mkAppN forallTerm xs))

/--
Given a monadic function `F` that takes a term and produces a new term,
lifts this to the monadic function that opens a `∀` telescope, applies `F` to the body,
and then builds the lambda telescope term for the new term.
-/
def mapForallTelescope (F : Expr → MetaM Expr) (forallTerm : Expr) : MetaM Expr := do
  mapForallTelescope' (fun _ e => F e) forallTerm

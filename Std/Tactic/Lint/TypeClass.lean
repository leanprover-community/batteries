/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner
-/
import Std.Tactic.Lint.Basic
import Std.Data.Array.Basic

namespace Std.Tactic.Lint
open Lean Meta

/--
Lints for instances with arguments that cannot be filled in, like
```
instance {α β : Type} [Group α] : Mul α where ...
```
-/
@[std_linter] def impossibleInstance : Linter where
  noErrorsFound := "No instance has arguments that are impossible to infer"
  errorsFound := "SOME INSTANCES HAVE ARGUMENTS THAT ARE IMPOSSIBLE TO INFER
These are arguments that are not instance-implicit and do not appear in
another instance-implicit argument or the return type."
  test declName := do
    unless ← isInstance declName do return none
    forallTelescopeReducing (← inferType (← mkConstWithLevelParams declName)) fun args ty => do
    let argTys ← args.mapM inferType
    let impossibleArgs ← args.zipWithIndex.filterMapM fun (arg, i) => do
      let fv := arg.fvarId!
      if (← fv.getDecl).binderInfo.isInstImplicit then return none
      if ty.containsFVar fv then return none
      if argTys[i+1:].any (·.containsFVar fv) then return none
      return some m!"argument {i+1} {arg} : {← inferType arg}"
    if impossibleArgs.isEmpty then return none
    addMessageContextFull <| .joinSep impossibleArgs.toList ", "

/--
Returns out-params as well as other arguments that should be considered
out-params for the dangerous instances linter.  That is, arguments that
instances will always instantiate with metavariable-free terms (but not
necessarily a unique one).
-/
private def getOutParamPositionsOf (classTy : Expr) : CoreM (Array Nat) := do
  let .const className _ := classTy.getAppFn | return #[]
  if className == ``CoeHead then return #[1]
  if className == ``CoeTail then return #[0]
  if className == ``Coe then return #[0]
  return (getOutParamPositions? (← getEnv) className).getD #[]

/--
Lints for instances that produce subgoals with metavariables, like
```
instance [Group β] : Add α where ...
```
-/
@[std_linter] def dangerousInstance : Linter where
  noErrorsFound := "No instances are dangerous"
  errorsFound := "SOME INSTANCES ARE DANGEROUS
During type-class search, they produce subgoals like `Group ?M`.
Try marking the dangerous arguments as implicit instead."
  test declName := do
    unless ← isInstance declName do return none

    -- create both metavariables and free variables for the instance args
    let declTy ← inferType (← mkConstWithLevelParams declName)
    forallTelescopeReducing declTy fun argVars _ => do
    let (argMVars, argBIs, ty) ← forallMetaTelescopeReducing declTy

    -- assigns the metavariables in `e` with the corresponding free variables created above
    let assignMVarsIn (e : Expr) : MetaM Unit := do
      for mvarId in ← getMVars e do
        if let some i := argMVars.findIdx? (·.mvarId! == mvarId) then
          mvarId.assign argVars[i]!

    -- assign all metavariables in non-out-params of the return value
    -- (these are guaranteed to be assigned during TC search as well)
    let tyOutParams ← getOutParamPositionsOf ty
    for (tyArg, i) in ty.getAppArgs.zipWithIndex do
      unless tyOutParams.contains i do
        assignMVarsIn tyArg

    let mut dangerousArgs := #[]
    for argMVar in argMVars, argBI in argBIs, argVar in argVars, i in [:argMVars.size] do
      unless argBI == .instImplicit do continue
      let argTy ← instantiateMVars (← inferType argMVar)
      let argTyOutParams ← getOutParamPositionsOf argTy
      -- report any non-out-param arguments in subgoals that still contain mvars
      let isDangerous := argTy.getAppArgs.zipWithIndex.any fun (tcArg, i) =>
        !argTyOutParams.contains i && tcArg.hasExprMVar
      if isDangerous then
        dangerousArgs := dangerousArgs.push <|
          ← addMessageContextFull m!"argument {i+1} {argVar} : {argTy}"

      -- assume that the synthesizing the subgoal fills in the subgoals' out-params
      assignMVarsIn argTy

    unless dangerousArgs.isEmpty do
      return m!"generates subgoals with metavariables: {MessageData.joinSep dangerousArgs.toList ", "}"

    -- check that the out-params of the instance return type are all filled in
    let ty ← instantiateMVars ty
    for (tyArg, i) in ty.getAppArgs.zipWithIndex do
      if tyOutParams.contains i then
        if tyArg.hasExprMVar then
          return ← addMessageContextFull
            m!"unassigned metavariable in out-param: {ty}"

    return none

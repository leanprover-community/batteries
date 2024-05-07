/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/
import Batteries.Lean.Meta.Basic

open Lean Lean.Meta

namespace Lean.MVarId

/--
Instantiate metavariables in the type of the given metavariable, update the
metavariable's declaration and return the new type.
-/
def instantiateMVarsInType [Monad m] [MonadMCtx m] [MonadError m]
    (mvarId : MVarId) : m Expr := do
  let mdecl ← (← getMCtx).getExprMVarDecl mvarId
  let type := mdecl.type
  if type.hasMVar then
    let type ← instantiateMVars type
    let mdecl := { mdecl with type }
    modifyMCtx (·.declareExprMVar mvarId mdecl)
    return type
  else
    return type

/--
Instantiate metavariables in the `LocalDecl` of the given fvar, update the
`LocalDecl` and return the new `LocalDecl.`
-/
def instantiateMVarsInLocalDecl [Monad m] [MonadMCtx m] [MonadError m]
    (mvarId : MVarId) (fvarId : FVarId) : m LocalDecl := do
  let mdecl ← (← getMCtx).getExprMVarDecl mvarId
  let (some ldecl) := mdecl.lctx.find? fvarId | throwError
    "unknown fvar '{fvarId.name}' (in local context of mvar '?{mvarId.name}')"
  let ldecl ← Lean.instantiateLocalDeclMVars ldecl
  let mdecl :=
    { mdecl with lctx := mdecl.lctx.modifyLocalDecl fvarId fun _ => ldecl }
  modifyMCtx (·.declareExprMVar mvarId mdecl)
  return ldecl

/--
Instantiate metavariables in the local context of the given metavariable, update
the metavariable's declaration and return the new local context.
-/
def instantiateMVarsInLocalContext [Monad m] [MonadMCtx m] [MonadError m]
    (mvarId : MVarId) : m LocalContext := do
  let mdecl ← (← getMCtx).getExprMVarDecl mvarId
  let lctx ← instantiateLCtxMVars mdecl.lctx
  modifyMCtx (·.declareExprMVar mvarId { mdecl with lctx })
  return lctx

/--
Instantiate metavariables in the local context and type of the given
metavariable.
-/
def instantiateMVars [Monad m] [MonadMCtx m] [MonadError m] (mvarId : MVarId) :
    m Unit := do
  discard $ (← getMCtx).getExprMVarDecl mvarId
    -- The line above throws an error if the `mvarId` is not declared. The line
    -- below panics.
  instantiateMVarDeclMVars mvarId

end Lean.MVarId

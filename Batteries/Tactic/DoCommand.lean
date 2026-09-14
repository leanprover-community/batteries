/-
Copyright (c) 2026 Robin Arnez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Arnez
-/
module

public meta import Lean.Elab.Do.Basic
public meta import Lean.Meta.Eval
public meta import Batteries.Util.Incremental
public meta import Batteries.Util.Eval

public meta section

/-!
# The `#do` command

The `#do` command is like `run_cmd` but allows using variables from previous uses of `#do`.
Furthermore, `#do_meta` is like `#do` and shares its variable state while operating in `MetaM`.
Finally, `#clear_do` can be used to remove all variables from the current do state.
-/

namespace Batteries.Tactic.DoCommand

open Lean Meta Elab Command Do

/-- The part of the `DoCommandExtensionState` used for monad state -/
structure MonadStateStack where
  /-- The meta state used for `#do_meta` -/
  metaState : Meta.State := {}
deriving Inhabited

/-- The state for `#do` -/
structure DoCommandExtensionState where
  /--
  The current local context for `#do`.

  Invariant: `lctx` does not contain metavariables or level parameters or non-dependent `ldecl`s.
  -/
  lctx : LocalContext := {}
  /-- The local instances for `lctx` -/
  localInstances : LocalInstances := #[]
  /--
  The values associated to free variables in `lctx`.

  Invariant: every free variable in `lctx` has a corresponding value in `values`
  -/
  values : FVarIdMap NonScalar := {}
  /-- See `Lean.Elab.Do.Context.mutVars` -/
  mutVars : Array MutVar := #[]
  /-- See `Lean.Elab.Do.Context.mutVarDefs` -/
  mutVarDefs : Std.HashMap Name MutVar := {}
  /-- Monad state for use in e.g. `#do_meta` -/
  monadState : MonadStateStack := {}
deriving Inhabited

/-- The extension for `#do` -/
initialize doExtension : EnvExtension DoCommandExtensionState ←
  registerEnvExtension (pure {})

/-- Implementation detail of `#do` -/
abbrev Data := Array NonScalar

/-- Implementation detail of `#do` -/
unsafe def Data.getValue.{u} {α : Sort u} (vs : Data) (i : Nat) : α :=
  unsafeCast <| vs[i]'lcProof

@[inherit_doc Data.getValue]
unsafe def Data.getValueLetImpl.{u} {α : Sort u} (vs : Data) (i : Nat) (_v : α) : α :=
  unsafeCast <| vs[i]'lcProof

/-- Implementation detail of `#do` -/
@[implemented_by getValueLetImpl]
unsafe abbrev Data.getValueLet.{u} {α : Sort u} (_vs : Data) (_i : Nat) (v : α) : α := v

/-- Implementation detail of `#do` -/
def Data.empty : Data := #[]

/-- Implementation detail of `#do` -/
unsafe nonrec def Data.push.{u} {α : Sort u} (d : Data) (x : α) : Data := d.push (unsafeCast x)

/--
Given `value : type` which may depend on free variables in `state.lctx`, evaluates it to a value
of type `α` (assuming `type` is equivalent to `α`).
-/
unsafe def DoCommandExtensionState.eval (state : DoCommandExtensionState)
    (α : Type) (type : Expr) (value : Expr) (checkMeta := true)
    (allowSorry := false) (alternative? : Option String := none) : MetaM α := do
  if value.hasMVar then
    throwError "failed to evaluate expression, it contains metavariables{indentExpr value}"
  let fvars ← (collectFVars {} value).addDependencies
  let fvarsInOrder := state.lctx.getFVarIds.filter fvars.fvarSet.contains
  let value ← withLCtx state.lctx state.localInstances do
    withLocalDeclD `data (mkConst ``Data) fun data => do
      let mut newLCtx ← getLCtx -- including the `data` variable
      -- Replace local declarations in `fvarsInOrder` with `have` and `let` declarations
      for h : i in 0...fvarsInOrder.size do
        let fvar := fvarsInOrder[i]
        let u ← getLevel (← fvar.getType)
        newLCtx := newLCtx.modifyLocalDecl fvar fun
          | .cdecl idx fvar userName type bi kind =>
            let value := mkApp3 (.const ``Data.getValue [u]) type data (mkRawNatLit i)
            .ldecl idx fvar userName type value (nondep := true) kind
          | .ldecl idx fvar userName type value nondep kind =>
            let value := mkApp4 (.const ``Data.getValueLet [u]) type data (mkRawNatLit i) value
            .ldecl idx fvar userName type value nondep kind
      -- Note: The free variables are out of order here (`data` should be first)
      -- but `mkLetFVars` ignores the order as long as we don't have metavariables
      -- (which we don't have here, see check above)
      withLCtx' newLCtx do
        mkLetFVars (#[data] ++ fvarsInOrder.map Expr.fvar) value (generalizeNondepLet := false)
  let mut data : Data := .empty
  for fvar in fvarsInOrder do
    data := data.push (state.values.get! fvar)
  let f ← evalExprWithSorryCheck (Data → α) (.forallE `data (mkConst ``Data) type .default) value
    (safety := .unsafe) checkMeta allowSorry alternative?
  return f data

private def checkExpr (e : Expr) : TermElabM Expr := do
  let e ← instantiateMVars e
  if e.hasExprMVar then
    discard <| Term.logUnassignedUsingErrorInfos (← getMVars e)
    throwAbortTerm
  if e.hasLevelMVar then
    let lmvars := collectLevelMVars {} e
    discard <| Term.logUnassignedLevelMVarsUsingErrorInfos lmvars.result
    throwAbortTerm
  if e.hasLevelParam then
    throwError "Resulting expression has unexpected level parameters"
  return e

private def checkLCtx (lctx : LocalContext) : TermElabM LocalContext := do
  withLCtx lctx #[] do
    let mut lctx := lctx
    for decl in lctx do
      if decl.type.hasMVar || decl.type.hasLevelParam then
        lctx := lctx.setType decl.fvarId <| ← checkExpr decl.type
      if let some value := decl.value? then
        let newValue ← checkExpr value
        lctx := lctx.modifyLocalDecl decl.fvarId fun decl => decl.setValue newValue
      if decl.isNondep then
        lctx := lctx.modifyLocalDecl decl.fvarId fun
          | .ldecl idx fvar userName type _value (nondep := true) kind =>
            .cdecl idx fvar userName type .default kind
          | d => d
    return lctx

/-- Implementation detail of `#do` -/
structure ContinuationResult where
  /-- All new free variables in the order they are stored in the resulting array -/
  newFVars : Array FVarId
  /-- The new state, with updated local context and mutable variables -/
  newState : DoCommandExtensionState

/-- Continuation for adding new variables -/
private def continuation (ref : IO.Ref (Option ContinuationResult))
    (outerRef : Syntax) (state : DoCommandExtensionState) (resultName : Name) : DoElemCont where
  resultName
  resultType := mkConst ``Unit
  kind := .nonDuplicable
  k := do
    if (← ref.get).isSome then
      logWarningAt outerRef "The continuation got run twice. This is probably due to \
        https://github.com/leanprover/lean4/issues/13858"
      -- empty returns get handled in a special way in `elabDoCommandCore`
      return ← mkPureApp (mkConst ``Data) (mkConst ``Data.empty)
    let lctx ← getLCtx
    let localInstances ← getLocalInstances
    let mut newFVars := #[]
    let mut resExpr := mkConst ``Data.empty
    for decl in lctx do
      if state.lctx.contains decl.fvarId then
        continue
      newFVars := newFVars.push decl.fvarId
      let u ← getLevel decl.type
      resExpr := mkApp3 (.const ``Data.push [u]) decl.type resExpr decl.toExpr
    let { mutVars, mutVarDefs, .. } ← read
    let newState := { state with lctx, localInstances, mutVars, mutVarDefs }
    ref.set <| some { newFVars, newState }
    mkPureApp (mkConst ``Data) resExpr

/-- Monad-generic version of the `#do` command -/
def elabDoCommandCore (m : Type → Type)
    (lift : ∀ {α}, m α → MonadStateStack → CommandElabM (α × MonadStateStack))
    (mExpr : Expr) (doSeq : TSyntax ``Lean.Parser.Term.doSeq)
    (allowSorry : Bool) (alternative? : Option String := none) :
    CommandElabM Unit := do
  let extData := doExtension.getState (← getEnv)
  let outerRef ← getRef
  let (act, newFVars, newState) ← liftTermElabM do
    -- better give it any name than pollute the global namespace
    -- we can't just use `withoutModifyingEnv` because the auxiliary constants may be needed by
    -- further uses of `#do`
    Term.withDeclName (mkPrivateName (← getEnv) (← mkFreshUserName `_do)) do
    withLCtx extData.lctx extData.localInstances do
    let resultName ← mkFreshUserName `__x
    let ref : IO.Ref (Option ContinuationResult) ← IO.mkRef none
    let cont : DoElemCont := continuation ref outerRef extData resultName
    let monadInfo := { m := mExpr, u := 0, v := 0 }
    let ctx := {
      monadInfo
      doBlockResultType := mkConst ``Data
      contInfo := ContInfo.toContInfoRef {
        returnCont := {
          resultType := mkConst ``Unit
          k _ := mkPureApp (mkConst ``Data) (mkConst ``Data.empty)
        }
      }
      ops := DoOps.toDoOpsRef .default
      mutVars := extData.mutVars
      mutVarDefs := extData.mutVarDefs
    }
    let res ← ((elabDoSeq doSeq cont).run ctx)
    Term.synthesizeSyntheticMVarsNoPostponing
    let res ← checkExpr res
    let act ← unsafe extData.eval (m Data) (.app mExpr (mkConst ``Data)) res
      (checkMeta := !Elab.inServer.get (← getOptions)) allowSorry alternative?
    -- if the continuation didn't get run, that probably means we throw an error or return
    -- in that case, we just don't add new values below
    let ⟨newFVars, newState⟩ := (← ref.get).getD ⟨#[], extData⟩
    let newState := { newState with lctx := ← checkLCtx newState.lctx }
    withLCtx newState.lctx newState.localInstances do
      for fvar in newFVars do
        -- we have to invent original syntax to appease the unused variable linter :-(
        let substr := { str := "", startPos := 0, stopPos := 0 }
        Term.addTermInfo' (.atom (.original substr 0 substr 0) "") (.fvar fvar)
    return (act, newFVars, newState)
  -- Make sure that `IO.println` output is always in the right spot and capturable by `#guard_msgs`
  let (out, res) ← IO.FS.withIsolatedStreams
      (isolateStderr := Core.stderrAsMessages.get (← getOptions)) do
    observing <| lift act extData.monadState
  unless out.isEmpty do logInfo out
  match res with
  | .error e => throw e
  | .ok (res, monadState) =>
    if res.isEmpty && !newFVars.isEmpty then
      -- No new variables were added; either because of an early return or because of a
      -- continuation running twice. In this case using `newState` would break the invariant
      -- of `values` so we just keep the old variables but update the monad state
      modifyEnv (doExtension.modifyState · fun state => { state with monadState })
      return
    let mut newState := { newState with monadState }
    assert! res.size == newFVars.size
    for fvar in newFVars, val in res do
      newState := { newState with values := newState.values.insert fvar val }
    modifyEnv (doExtension.setState · newState)

/--
`#do code` runs `code` with access to all variables from previous `#do` (and `#do_meta`)
invocations. Example:
```
#do let x ← IO.rand 0 100
-- these will both print the same number
#do IO.println x
#do IO.println x
```
This command can be used to run expensive computations once and refer to them later.

For `#do`, the body is run in the `CommandElabM` monad. For an alternative where computations run
in `MetaM`, use `#do_meta`.
-/
syntax (name := doCommand) "#do " doSeq : command

/-- An alternative to `#do` that doesn't check for `sorry`s -/
syntax (name := doBangCommand) "#do! " doSeq : command

private def liftCommand (act : CommandElabM α) (stateStack : MonadStateStack) :
    CommandElabM (α × MonadStateStack) := return (← act, stateStack)

@[command_elab doCommand, inherit_doc doCommand, incremental]
def elabDoCommand : CommandElab := simpleIncrementalElab fun stx => do
  let `(#do%$tk $seq) := stx | throwUnsupportedSyntax
  withRef tk <| elabDoCommandCore CommandElabM liftCommand (mkConst ``CommandElabM) seq
    (allowSorry := false) (alternative? := "#do!")

@[command_elab doBangCommand, inherit_doc doBangCommand, incremental]
def elabDoBangCommand : CommandElab := simpleIncrementalElab fun stx => do
  let `(#do!%$tk $seq) := stx | throwUnsupportedSyntax
  withRef tk <| elabDoCommandCore CommandElabM liftCommand (mkConst ``CommandElabM) seq
    (allowSorry := true)

/--
`#do_meta code` runs `code` with access to all variables from previous `#do` and `#do_meta`
invocations in the `MetaM` monad. Example:
```
#do_meta let x ← IO.rand 0 100
-- these will both print the same number
#do_meta IO.println x
#do_meta IO.println x
```
This command can be used to run expensive computations once and refer to them later.

For an alternative where computations run in `CommandElabM`, use `#do`.
-/
syntax (name := doMetaCommand) "#do_meta " doSeq : command

/-- An alternative to `#do_meta` that doesn't check for `sorry`s -/
syntax (name := doMetaBangCommand) "#do_meta! " doSeq : command

private def liftMeta (act : MetaM α) (stateStack : MonadStateStack) :
    CommandElabM (α × MonadStateStack) :=
  liftCoreM do
    let (res, state) ← act.run {} stateStack.metaState
    -- we can't keep the cache since commands in between `#do_meta` calls might
    -- e.g. introduce new instances
    return (res, { stateStack with metaState := { state with cache := {} } })

@[command_elab doMetaCommand, inherit_doc doMetaCommand, incremental]
def elabDoMetaCommand : CommandElab := simpleIncrementalElab fun stx => do
  let `(#do_meta%$tk $seq) := stx | throwUnsupportedSyntax
  withRef tk <| elabDoCommandCore MetaM liftMeta (mkConst ``MetaM) seq
    (allowSorry := false) (alternative? := "#do_meta!")

@[command_elab doMetaBangCommand, inherit_doc doMetaBangCommand, incremental]
def elabDoMetaBangCommand : CommandElab := simpleIncrementalElab fun stx => do
  let `(#do_meta!%$tk $seq) := stx | throwUnsupportedSyntax
  withRef tk <| elabDoCommandCore MetaM liftMeta (mkConst ``MetaM) seq (allowSorry := true)

/--
Clears all variables from the current `#do` context.
-/
elab "#clear_do" : command => do
  modifyEnv (doExtension.setState · {})

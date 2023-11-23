/-
Copyright (c) 2021 Gabriel Ebner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner
-/
import Lean.Elab.Command
import Lean.Elab.SetOption

namespace Lean
open Elab Command MonadRecDepth Meta

/--
Lift an action in `CommandElabM` into `CoreM`, updating the traces and the environment.
This does not preserve things like `open` and `namespace` declarations.
-/
def liftCommandElabM (k : CommandElabM α) : CoreM α := do
  let (a, commandState) ←
    k.run {
      fileName := ← getFileName
      fileMap := ← getFileMap
      ref := ← getRef
      tacticCache? := none
    } |>.run {
      env := ← getEnv
      maxRecDepth := ← getMaxRecDepth
      scopes := [{ header := "", opts := ← getOptions }]
    }
  modify fun coreState => { coreState with
    traceState.traces := coreState.traceState.traces ++ commandState.traceState.traces
    env := commandState.env
  }
  if let some err := commandState.messages.msgs.toArray.find? (·.severity matches .error) then
    throwError err.data
  pure a

/--
Runs a `CoreM` action in `CommandElabM`.

This is a bit of a hack! We try to translate as much information as possible,
but this should be used with some caution as it is not the intended usage!

* Copies as much as possible of the `Command.State` to
  a `Core.State` (this drops `nextInstIdx` and `scopes`),
* Copies as much as possible of the `Command.context` to a `CoreCcontext`,
  (this drops `cmdPos`, `macroStack`, and `tacticCache`).
* Copies as much as possible from the head `Scope` in `Command.State.scopes` to the `Core.Context`.
* Uses default values in the `Core.context` for `initHeartbeats`, `maxHeartbeats`).
* Copies the `Commmand.State.maxRecDepth` to the `Core.Context.maxRecDepth`.

After executing the `CoreM` action, we then copy the `Core.State` back into the `Command.State`
(preserving the original values of `scopes` and `maxRecDepth`, which were read only in `CoreM`).
-/
def Elab.Command.runCore (x : CoreM α) : CommandElabM α := do
  let headScope := (← get).scopes.head?.getD { header := "" }
  let (a, s) ← Core.CoreM.toIO x
    { (← read) with
      options := headScope.opts
      currNamespace := headScope.currNamespace
      openDecls := headScope.openDecls
      maxRecDepth := (← get).maxRecDepth }
    { (← get) with }
  modify fun t =>
  ({ s with
     scopes := t.scopes
     maxRecDepth := t.maxRecDepth} : Command.State)
  return a

/--
Runs a `MetaM` action in `CommandElabM`, using fresh `MetaM` state and context,
and relying on `Lean.Elab.Command.runCoreM` to translate `CoreM` state and context to
the extent possible; see the doc-string there for caveats.
-/
def Elab.Command.runMeta (x : MetaM α) : CommandElabM α := do
  (·.1) <$> Core.CoreM.toIO (MetaM.run' x) { (← read) with } { (← get) with }

/--
Evaluate any `set_option in` commands before the given `stx`, and pass the inner `stx` with the
updated environment to the continuation `k`.
-/
partial def withSetOptionIn (k : CommandElab) : CommandElab := fun stx => do
  if stx.getKind == ``Lean.Parser.Command.in &&
     stx[0].getKind == ``Lean.Parser.Command.set_option then
      let opts ← Elab.elabSetOption stx[0][1] stx[0][2]
      Command.withScope (fun scope => { scope with opts }) do
        withSetOptionIn k stx[1]
  else
    k stx

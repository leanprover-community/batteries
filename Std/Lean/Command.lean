/-
Copyright (c) 2021 Gabriel Ebner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner
-/
import Lean.Elab.Command
import Lean.Elab.SetOption

namespace Lean
open Elab Command MonadRecDepth

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

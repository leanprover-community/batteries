/-
Copyright (c) 2026 Robin Arnez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Arnez
-/
module

public meta import Lean.Elab.Command

/-!
# A utility for simple incremental commands
-/

open Lean Elab Command

public meta section

namespace Batteries.Tactic

/-- A snapshot for the result of command elaboration -/
structure CommandElabResultSnapshot extends Language.Snapshot where
  /-- The syntax that was being elaborated -/
  stx : Syntax
  /-- The state after command elaboration -/
  state : Command.State
  /-- The exception thrown during command elaboration, if any -/
  error? : Option Exception
  /-- Snapshot tasks produced by `logSnapshotTask` during command elaboration -/
  moreSnaps : Array (Language.SnapshotTask Language.SnapshotTree)
deriving Nonempty

/-- The snapshot type for `simpleIncrementalElab` -/
structure SimpleIncrementalSnapshot extends Language.Snapshot where
  /-- The result for the previous execution of the command -/
  result : Language.SnapshotTask (Option CommandElabResultSnapshot)
  /-- The last result that didn't error because of missing syntax -/
  lastNoSyntaxErrorResult? : Option CommandElabResultSnapshot
deriving TypeName

instance : Language.ToSnapshotTree CommandElabResultSnapshot where
  toSnapshotTreeM snap :=
    return ⟨← snap.toSnapshot.transform, ← snap.moreSnaps.mapM (·.transform)⟩

instance : Language.ToSnapshotTree SimpleIncrementalSnapshot where
  toSnapshotTreeM snap := do
    let mut subsnaps := #[← snap.result.transform]
    if let some x := snap.lastNoSyntaxErrorResult? then
      subsnaps := subsnaps.push (.finished x.stx (← Language.toSnapshotTreeM x))
    return ⟨← snap.toSnapshot.transform, subsnaps⟩

/--
Wraps `cmd` with simple incrementality handling that makes the command not re-run if only trailing
whitespace was changed or when a syntax error gets introduced and then removed again.

To make this work, `cmd` doesn't receive the trailing whitespace of the command and doesn't have
access to incrementality itself.

To make use of this, you have to write an explicit elaborator (i.e. a declaration with a
`@[command_elab]`) and tag it with `@[incremental]` and then wrap the body in
`simpleIncrementalElab`. Example:
```
syntax (name := expensiveCmd) "#expensive_command" : command

@[command_elab expensiveCmd, incremental]
def elabExpensiveCmd : CommandElab := simpleIncrementalElab fun stx => do
  ...
```
-/
def simpleIncrementalElab (cmd : CommandElab) : CommandElab := fun stx => do
  let stx := stx.unsetTrailing
  let snap? := (← read).snap?
  let mut oldSnap? := none
  let mut lastNoSyntaxErrorResult? := none
  if let some old := snap?.bind (·.old?) then
    -- the top-level snapshot is cheap to get
    if let some val := old.val.get.toTyped? SimpleIncrementalSnapshot then
      -- if the previous version of the command had the same syntax, just reuse it
      if old.stx.unsetTrailing.eqWithInfo stx then
        oldSnap? := val.result.get
      -- otherwise, we look for a previous successful run
      else if let some res := val.lastNoSyntaxErrorResult? then
        if res.stx.eqWithInfo stx then
          oldSnap? := some res
      lastNoSyntaxErrorResult? := val.lastNoSyntaxErrorResult?
      -- If the last task has finished successfully (for example, because of waiting on it above)
      -- then mark it as the `lastNoSyntaxErrorResult?`
      if ← IO.hasFinished val.result.task then
        if let some res := val.result.task.get then
          -- we want to also avoid re-elaboration on non-syntax errors because they likely
          -- correspond to failed but potentially expensive computations
          if res.error?.isNone || !res.stx.hasMissing then
            lastNoSyntaxErrorResult? := res
  -- if we don't have syntax errors, don't bother saving a `lastNoSyntaxErrorResult?`
  -- since the new run will already become a result without syntax errors
  -- and saving the data from the previous run would only retain a potentially large amount
  -- of memory for longer
  unless stx.hasMissing do
    lastNoSyntaxErrorResult? := none
  -- commit the cheap parts of the snapshot (i.e. the `lastNoSyntaxErrorResult?`)
  let promise : IO.Promise CommandElabResultSnapshot ← IO.Promise.new
  if let some snap := snap? then
    snap.new.resolve <| .ofTyped {
      diagnostics := .empty
      result := {
        stx? := stx
        cancelTk? := (← read).cancelTk?
        task := promise.result?
      }
      lastNoSyntaxErrorResult?
      : SimpleIncrementalSnapshot
    }
  -- re-run if necessary
  let newSnap ← oldSnap?.getDM do
    -- don't leak `snap?` to the command elaborator
    let error? ← withReader ({ · with snap? := none }) do observing <| withRef stx (cmd stx)
    let moreSnaps ← modifyGet fun s => (s.snapshotTasks, { s with snapshotTasks := #[] })
    return {
      diagnostics := .empty
      stx
      state := ← get
      error? := match error? with | .error x => some x | _ => none
      moreSnaps
    }
  set newSnap.state
  -- and finally, register the result
  promise.resolve newSnap
  if let some err := newSnap.error? then
    throw err

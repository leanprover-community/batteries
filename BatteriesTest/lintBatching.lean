import Batteries.Tactic.Lint

open Lean Meta Batteries.Tactic.Lint

/-! Regression tests for batched environment linting. -/

-- A worker count of zero (for example from `LEAN_NUM_THREADS=0`) still runs every job.
run_meta do
  let results ← mapOnWorkers (Array.range 10) 0 fun i => return i
  unless results.qsort (· < ·) == Array.range 10 do throwError "jobs dropped: {results}"

-- Each check sees fresh Core and Meta state and a fresh name generator. Every check runs once,
-- and an exception becomes `LINTER FAILED`.
run_meta do
  let originalModule := (← getEnv).mainModule
  let names ← IO.mkRef ({} : Std.HashSet Name)
  let test : Batteries.Tactic.Lint.Linter := {
    noErrorsFound := ""
    errorsFound := ""
    test := fun decl => do
      unless (← getEnv).mainModule == originalModule do
        throwError "Core state leaked between checks"
      unless (← getMCtx).decls.isEmpty do
        throwError "Meta state leaked between checks"
      let mvar ← mkFreshExprMVar (mkSort .zero)
      let fresh ← names.modifyGet fun seen =>
        (!seen.contains mvar.mvarId!.name, seen.insert mvar.mvarId!.name)
      unless fresh do throwError "name generator reused between checks"
      modifyEnv (·.setMainModule `Modified)
      let .num _ i := decl | throwError "unexpected declaration name"
      if i % 5 == 0 then throwError "expected exception"
      return if i % 7 == 0 then some m!"expected failure" else none
  }
  let linters : Array NamedLinter := #[
    { test with name := `one, declName := `one },
    { test with name := `two, declName := `two }]
  -- Cross several batch boundaries, including an incomplete final batch.
  let decls := (Array.range (4 * lintBatchSize + 1)).map (Name.num `batch)
  let results ← lintCore decls linters
  unless results.size == 2 do throwError "wrong number of linters"
  for (_, failures) in results do
    for h : i in [:decls.size] do
      let expected? : Option String :=
        if i % 5 == 0 then some "LINTER FAILED:\nexpected exception"
        else if i % 7 == 0 then some "expected failure"
        else none
      let actual? ← failures[decls[i]]?.mapM (·.toString)
      unless actual? == expected? do
        throwError "unexpected result for {decls[i]}: {actual?}"
  unless (← names.get).size == 2 * decls.size do throwError "checks were skipped"

-- A `nolint` attribute skips the linter that it names.
@[nolint docBlame]
def batchingIgnored := 1

def batchingChecked := 2

run_meta do
  let test : NamedLinter := {
    name := `docBlame, declName := `docBlame
    noErrorsFound := "", errorsFound := ""
    test := fun _ => return some m!"checked" }
  let results ← lintCore #[``batchingIgnored, ``batchingChecked] #[test]
  let some (_, failures) := results[0]? | throwError "missing linter result"
  unless failures.size == 1 && failures.contains ``batchingChecked do
    throwError "nolint attribute ignored"

-- Each check uses half of the heartbeat budget, so the test fails if checks share one budget.
run_meta do
  let test : NamedLinter := {
    name := `heartbeats, declName := `heartbeats
    noErrorsFound := "", errorsFound := ""
    test := fun _ => do
      IO.addHeartbeats 10000
      Core.checkMaxHeartbeats "lint test"
      return none }
  let results ← withTheReader Core.Context (fun ctx => { ctx with maxHeartbeats := 20000 }) <|
    lintCore #[`first, `second] #[test]
  let some (_, failures) := results[0]? | throwError "missing linter result"
  unless failures.isEmpty do throwError "checks shared a heartbeat budget"

-- A token set before the run stops the workers before any check runs.
run_meta do
  let called ← IO.mkRef false
  let test : NamedLinter := {
    name := `cancelled, declName := `cancelled
    noErrorsFound := "", errorsFound := ""
    test := fun _ => do called.set true; return none }
  let token ← IO.CancelToken.new
  token.set
  let action ← Core.wrapAsync (fun _ => lintCore #[`cancelled] #[test]) (some token)
  let result ← action () |>.toBaseIO
  match result with
  | .error ex => unless ex.isInterrupt do throwError "unexpected exception"
  | .ok _ => throwError "cancellation was ignored"
  if ← called.get then throwError "check ran after cancellation"

-- An interrupt inside a check propagates and does not become a `LINTER FAILED` message.
run_meta do
  let token ← IO.CancelToken.new
  let test : NamedLinter := {
    name := `cancelled, declName := `cancelled
    noErrorsFound := "", errorsFound := ""
    test := fun _ => do
      token.set
      Core.checkInterrupted
      return none }
  let action ← Core.wrapAsync (fun _ => lintCore #[`cancelled] #[test]) (some token)
  match ← action () |>.toBaseIO with
  | .error ex => unless ex.isInterrupt do throwError "unexpected exception"
  | .ok _ => throwError "cancellation became a linter warning"

import Batteries.Tactic.Lint

/-!
Tests `lintCore`'s `localDecls`: local linters (`Linter.isLocal`) lint only those declarations,
while the other linters still lint all of them.
-/

open Lean Elab Command Batteries.Tactic.Lint

/-- A local linter that flags every declaration it is given. -/
@[env_linter disabled] def flagAllLocal : Batteries.Tactic.Lint.Linter where
  noErrorsFound := "none"
  errorsFound := "flagged"
  isLocal := true
  test _ := pure (some "flagged")

/-- A global linter that flags every declaration it is given. -/
@[env_linter disabled] def flagAllGlobal : Batteries.Tactic.Lint.Linter where
  noErrorsFound := "none"
  errorsFound := "flagged"
  test _ := pure (some "flagged")

/-- info: [(flagAllGlobal, 2), (flagAllLocal, 1)] -/
#guard_msgs in
run_cmd liftCoreM do
  let linters := #[← getLinter `flagAllGlobal ``flagAllGlobal,
    ← getLinter `flagAllLocal ``flagAllLocal]
  let results ← lintCore #[``Nat.add, ``Nat.mul] linters (localDecls := some #[``Nat.add])
  logInfo m!"{results.toList.map fun (l, msgs) => (l.name, msgs.size)}"

/-- info: [(flagAllGlobal, 2), (flagAllLocal, 2)] -/
#guard_msgs in
run_cmd liftCoreM do
  let linters := #[← getLinter `flagAllGlobal ``flagAllGlobal,
    ← getLinter `flagAllLocal ``flagAllLocal]
  let results ← lintCore #[``Nat.add, ``Nat.mul] linters
  logInfo m!"{results.toList.map fun (l, msgs) => (l.name, msgs.size)}"

-- The local declaration array need not be a subset of the full array.
/-- info: [(flagAllGlobal, 1), (flagAllLocal, 1)] -/
#guard_msgs in
run_cmd liftCoreM do
  let linters := #[← getLinter `flagAllGlobal ``flagAllGlobal,
    ← getLinter `flagAllLocal ``flagAllLocal]
  let results ← lintCore #[``Nat.add] linters (localDecls := some #[``Nat.mul])
  let some (_, globalMsgs) := results[0]? | throwError "missing global result"
  let some (_, localMsgs) := results[1]? | throwError "missing local result"
  unless globalMsgs.contains ``Nat.add && localMsgs.contains ``Nat.mul do
    throwError "wrong declaration set"
  logInfo m!"{results.toList.map fun (l, msgs) => (l.name, msgs.size)}"

-- An empty local declaration array runs the local linters on no declarations.
/-- info: [(flagAllGlobal, 1), (flagAllLocal, 0)] -/
#guard_msgs in
run_cmd liftCoreM do
  let linters := #[← getLinter `flagAllGlobal ``flagAllGlobal,
    ← getLinter `flagAllLocal ``flagAllLocal]
  let results ← lintCore #[``Nat.add] linters (localDecls := some #[])
  logInfo m!"{results.toList.map fun (l, msgs) => (l.name, msgs.size)}"

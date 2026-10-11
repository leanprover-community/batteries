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

import Batteries.Tactic.Lint -- deprecated_module: ignore

/-! Tests that the deprecated `Batteries.Tactic.Lint` names still work. -/

open Lean Batteries.Tactic.Lint

/--
warning: `Batteries.Tactic.Lint.Linter` has been deprecated: Use `Batteries.Linter` instead
-/
#guard_msgs (substring := true) in
example : Type := Batteries.Tactic.Lint.Linter

set_option linter.deprecated false

/-- A linter declared with the deprecated type. -/
@[env_linter disabled] meta def oldStyle : Batteries.Tactic.Lint.Linter where
  noErrorsFound := "none"
  errorsFound := "flagged"
  test n := pure <| if n == ``Nat.add then some "flagged" else none

/-- info: [(oldStyle, 1)] -/
#guard_msgs in
run_cmd Elab.Command.liftCoreM do
  let l ← getLinter `oldStyle ``oldStyle
  let results ← lintCore #[``Nat.add, ``Nat.mul] #[l]
  logInfo m!"{results.toList.map fun (l, msgs) => (l.name, msgs.size)}"

#guard (LintVerbosity.low : Batteries.Linter.LintVerbosity) == .low

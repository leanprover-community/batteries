import Batteries.Tactic.Lint

open Lean Batteries.Tactic.Lint

/-- A linter that always throws, to test `LINTER FAILED` reporting. -/
@[env_linter disabled] def alwaysThrows : Batteries.Tactic.Lint.Linter where
  noErrorsFound := "No errors."
  errorsFound := "ERRORS:"
  test _ := throwError "boom"

/-- A declaration to lint. -/
def lintFailTestDecl : Nat := 1
/--
error: /- The `alwaysThrows` linter reports:
ERRORS:
This linter can be disabled with `@[nolint alwaysThrows]`. -/
#check alwaysThrows /- LINTER FAILED:
boom -/
#check lintFailTestDecl /- LINTER FAILED:
boom -/
-/
#guard_msgs in
#lint- only alwaysThrows

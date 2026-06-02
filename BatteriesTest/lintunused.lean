import Batteries.Tactic.Lint

-- should be ignored as the proof contains sorry
/-- warning: declaration uses `sorry` -/
#guard_msgs in
def foo (h : 1 = 1) : Bool := sorry

-- should be ignored since it uses `_h`
def foo' (_h : 1 = 1) : Bool := true

-- should not be ignored
def fooBad (h : 1 = 1) : Bool := true

/--
error: /- The `unusedArguments` linter reports:
UNUSED ARGUMENTS.
This linter can be disabled with `@[nolint unusedArguments]`. -/
#check fooBad /- argument 1: h : 1 = 1 -/
-/
#guard_msgs in
#lint- only unusedArguments

import Batteries.Tactic.Lint

-- should be ignored as the proof contains sorry
/-- warning: declaration uses `sorry` -/
#guard_msgs in
def foo (h : 1 = 1) : Bool := sorry

-- should be ignored since it uses `_h`
def foo' (_h : 1 = 1) : Bool := true

-- should not be ignored
set_option linter.unusedVariables false in
def fooBad (h : 1 = 1) : Bool := true

theorem foo1_ok (_h : 1 = 2) : True := trivial

set_option linter.unusedVariables false in
theorem foo2_bad (h : 1 = 1) : True := trivial

theorem foo3_bad [Mul Nat] : True := trivial

set_option linter.unusedVariables false in
theorem foo4_bad [h : Mul Nat] : True := trivial

theorem foo5_ok [_h : Mul Nat] : True := trivial

theorem foo6_ok (_ : Nat) : True := trivial

/--
error: /- The `unusedArguments` linter reports:
UNUSED ARGUMENTS.
This linter can be disabled with `@[nolint unusedArguments]`. -/
#check fooBad /- argument 1: h : 1 = 1 -/
#check foo2_bad /- argument 1: h : 1 = 1 -/
#check @foo3_bad /- argument 1: inst✝ : Mul Nat -/
#check @foo4_bad /- argument 1: h : Mul Nat -/
-/
#guard_msgs in
#lint- only unusedArguments

module

public import Batteries.Linter.UnnecessarySeqFocus

-- Warn when `<;>` leaves exactly 1 goal.
/--
@ +1:33...36
warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
-/
#guard_msgs (positions := true) in
example : True ∧ True := by skip <;> simp

-- `<;>` leaves 2 goals
example : True ∧ True := by constructor <;> simp

-- `<;>` leaves 0 goals
example : True ∧ True := by simp <;> simp

-- `<;>` leaves 1 and 2 goals in the two different branches.
example : True ∧ True ∧ True := by
  constructor
  all_goals (try apply And.intro) <;> simp

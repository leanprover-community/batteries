import Std.Linter.Focus
import Std.Tactic.GuardMsgs

/-- warning: this tactic is unfocused [linter.focus] -/
#guard_msgs in
example : 1 = 1 ∧ 2 = 2 := by
  skip
  constructor
  rfl
  rfl

#guard_msgs in
example : 1 = 1 ∧ 2 = 2 := by
  constructor
  · rfl
  rfl

#guard_msgs in
example : 1 = 1 ∧ 2 = 2 := by
  constructor <;> rfl

#guard_msgs in
example : 1 = 1 ∧ 2 = 2 := by
  constructor
  all_goals rfl

#guard_msgs in
example : 1 = 1 ∧ 2 = 2 := by
  constructor
  any_goals rfl

/--
warning: declaration uses 'sorry'
---
warning: this tactic is unfocused [linter.focus]
-/
#guard_msgs in
example : 1 = 1 ∧ 2 = 3 := by
  constructor
  any_goals rfl
  sorry

/-- warning: declaration uses 'sorry' -/
#guard_msgs in
example : 1 = 2 ∧ 2 = 2 := by
  constructor
  any_goals rfl
  sorry

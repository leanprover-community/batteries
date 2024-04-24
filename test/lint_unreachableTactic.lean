import Std.Linter.UnreachableTactic

/--
warning: this tactic is never executed
note: this linter can be disabled with `set_option linter.unreachableTactic false`
-/
#guard_msgs in
example : 1 = 1 := by
  rfl <;> simp

/--
warning: declaration uses 'sorry'
-/
#guard_msgs in
example : 1 = 1 := by
  stop
  rfl

#guard_msgs (drop warning) in
def t : Nat → Nat := sorry

#guard_msgs (drop warning) in
@[simp]
theorem a : aa = 0 → t aa = 0 := sorry

#guard_msgs in
example (ha : aa = 0) : t aa = 0 := by
  simp (disch := assumption)

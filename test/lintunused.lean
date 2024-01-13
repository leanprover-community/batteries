import Std.Tactic.Lint
import Std.Tactic.GuardMsgs

-- should be ignored as the proof contains sorry
/-- warning: declaration uses 'sorry' -/
#guard_msgs in
theorem Foo (h : 1 = 1) : True :=
  sorry

#lint- only unusedArguments

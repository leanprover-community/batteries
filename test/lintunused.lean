import Std.Tactic.Lint

-- should be ignored as the proof contains sorry
theorem Foo (h : 1 = 1) : True :=
  sorry

#lint- only unusedArguments

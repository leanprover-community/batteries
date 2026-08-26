-- Test: core does not currently provide DecidableEq for Except.
-- If this test fails, it means core now provides DecidableEq for Except
-- and the Batteries instance in Batteries.Lean.Except should be removed.

/--
error: failed to synthesize instance of type class
  DecidableEq (Except ?m.1 ?m.2)

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
#check (inferInstance : DecidableEq (Except _ _))

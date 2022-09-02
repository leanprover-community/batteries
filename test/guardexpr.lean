import Std.Tactic.GuardExpr

example (n : Nat) : Nat := by
  guard_hyp n : Nat
  let m : Nat := 1
  guard_hyp m := 1
  guard_hyp m : Nat := 1
  guard_target == Nat
  exact 0

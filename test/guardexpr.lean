import Std.Tactic.GuardExpr
import Std.Tactic.Basic

example (n : Nat) : Nat := by
  guard_hyp n : Nat
  let m : Nat := 1
  guard_expr 1 == (by exact 1)
  fail_if_success guard_expr 1 == (by exact 2)
  guard_hyp m := 1
  guard_hyp m : Nat := 1
  guard_target == Nat
  have : 1 = 1 := by conv =>
    guard_hyp m := 1
    guard_expr ‹Nat› == m
    fail_if_success guard_target == 1
    lhs
    guard_target == 1
  exact 0

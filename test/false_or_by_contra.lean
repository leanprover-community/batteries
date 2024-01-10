import Std.Tactic.FalseOrByContra
import Std.Tactic.GuardExpr

example (w : False) : False := by
  false_or_by_contra
  guard_target = False
  exact w

example (_ : False) : x ≠ y := by
  false_or_by_contra <;> rename_i h
  guard_hyp h : x = y
  guard_target = False
  simp_all

example (_ : False) : ¬ P := by
  false_or_by_contra <;> rename_i h
  guard_hyp h : P
  guard_target = False
  simp_all

example {P : Prop} (_ : False) : P := by
  false_or_by_contra <;> rename_i h
  guard_hyp h : ¬ P
  guard_target = False
  simp_all

-- It doesn't make sense to use contradiction if the goal is a Type (rather than a Prop).
example {P : Type} (_ : False) : P := by
  false_or_by_contra
  fail_if_success
    have : ¬ P := by assumption
  guard_target = False
  simp_all

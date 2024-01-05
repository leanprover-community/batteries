import Std.Tactic.FalseOrByContra
import Std.Tactic.GuardExpr

example (h : False) : False := by
  false_or_by_contra
  guard_target = False
  exact h

example (h : False) : x ≠ y := by
  false_or_by_contra <;> rename_i h
  guard_hyp h : x = y
  guard_target = False
  simp_all

example (h : False) : ¬ P := by
  false_or_by_contra <;> rename_i h
  guard_hyp h : P
  guard_target = False
  simp_all

example (h : False) : P := by
  false_or_by_contra <;> rename_i h
  guard_hyp h : ¬ P
  guard_target = False
  simp_all

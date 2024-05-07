import Batteries.Tactic.Basic

private axiom test_sorry : ∀ {α}, α

example {A} (h : False) : A := by
  exfalso
  exact h

example {A} : False → A := by
  exfalso
  show False -- exfalso is not supposed to close the goal yet
  exact test_sorry

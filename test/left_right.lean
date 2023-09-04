import Std.Tactic.LeftRight

/-- Construct a natural number using `left`. -/
def zero : Nat := by
  left

example : zero = 0 := rfl

/-- Construct a natural number using `right`. -/
def two : Nat := by
  right
  exact 1

example : two = 2 := rfl

example : Sum Nat (List Nat) := by
  left
  exact zero

example : Sum Nat (List Nat) := by
  right
  exact [0]

example : (1 = 1) ∨ (2 = 3) := by
  left
  rfl

example : (1 = 2) ∨ (3 = 3) := by
  right
  rfl

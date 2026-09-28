import Batteries.Tactic.PermuteGoals
import Batteries.Tactic.Unreachable

example (p q r : Prop) : p → q → r → p ∧ q ∧ r := by
  intros
  constructor
  on_goal 2 =>
    guard_target = q ∧ r
    constructor
    assumption
    -- Note that we have not closed all the subgoals here.
  guard_target = p
  assumption
  guard_target = r
  assumption

example (p q r : Prop) : p → q → r → p ∧ q ∧ r := by
  intros a b c
  constructor
  fail_if_success on_goal -3 => unreachable!
  fail_if_success on_goal -1 => exact a
  fail_if_success on_goal 0 => unreachable!
  fail_if_success on_goal 2 => exact a
  fail_if_success on_goal 3 => unreachable!
  on_goal 1 => exact a
  constructor
  swap
  exact c
  exact b

example (p q r : Prop) : p → q → r → p ∧ q ∧ r := by
  intros; constructor
  on_goal 2 => constructor
  on_goal 1 3 => assumption
  guard_target = q
  assumption

example (p q r : Prop) : p → q → r → p ∧ q ∧ r := by
  intros; constructor
  on_goal -1 => constructor
  on_goal -1 -3 => assumption
  guard_target = q
  assumption

-- The order of goals is preserved by `on_goal`
example : 1 = 1 ∧ 2 = 2 ∧ 3 = 3 := by
  refine ⟨?_, ?_, ?_⟩
  on_goal 1 3 => apply Nat.le_antisymm
  · exact Nat.le_refl 1
  · exact Nat.le_refl 1
  · rfl
  · exact Nat.le_refl 3
  · exact Nat.le_refl 3

example (p q : Prop) : p → q → p ∧ q := by
  intros a b
  constructor
  fail_if_success pick_goal -3
  fail_if_success pick_goal 0
  fail_if_success pick_goal -0
  fail_if_success pick_goal 3
  pick_goal -1
  exact b
  exact a

example (p : Prop) : p → p := by
  intros
  fail_if_success swap -- can't swap with a single goal
  assumption

example : 1 = 1 ∧ 2 = 2 ∧ 3 = 3 ∧ 4 = 4 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  pick_goal 3
  pick_goal 4
  · exact Eq.refl 4
  · exact Eq.refl 3
  · exact Eq.refl 1
  · exact Eq.refl 2

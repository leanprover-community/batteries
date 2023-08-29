import Std.Tactic.Case
import Std.Tactic.GuardExpr

set_option linter.missingDocs false

example (h : x = y) (h' : z = w) : x = y ∧ z = w := by
  constructor
  fail_if_success show z = z
  case _ : z = _
  · exact h'
  exact h

example (h : x = y) (h' : z = w) : x = y ∧ z = w := by
  constructor
  case _ : z = _ =>
    exact h'
  case left =>
    exact h

example (h : x = y) (h' : z = w) : x = y ∧ z = w := by
  constructor
  case _ : z = _ | left => assumption

example (h : x = y) (h' : z = w) : x = y ∧ z = w := by
  constructor
  case _ : z = _ => ?foo
  case foo =>
    exact h'
  case left =>
    exact h

example (h : x = y) (h' : z = w) : x = y ∧ z + 0 = w := by
  constructor
  case right : z = _ =>
    guard_target =ₛ z = w
    exact h'
  case _ : x = y := h

example (h : x = y) : x = y ∧ x = y := by
  constructor
  case _ : x = y | _ : x = y => ?foo
  -- Closes both
  case foo => exact h

example (h : x = y) : x = y ∧ x = y ∧ x = y := by
  refine ⟨?foo, ?_, ?_⟩
  · exact h
  case _ : x = y | _ : x = y => ?foo
  -- This metavariable was already assigned, so no more goals.

example (h : x = y) (h' : z = w) : x = y ∧ z + 0 = w := by
  constructor
  case _ : z = _ =>
    guard_target =ₛ z = w
    exact h'
  case left =>
    exact h

example (x y z : α) (h : x = y) (h' : y = z) : x = z := by
  apply Eq.trans
  case _ : α := y
  -- Note: `case` inserts a `let_fun` due to the fact it's implemented with `show`
  · guard_target =ₛ x = let_fun this := y; this
    exact h
  · guard_target = y = z
    exact h'

def Injective (f : α → β) : Prop := ∀ ⦃a₁ a₂⦄, f a₁ = f a₂ → a₁ = a₂

theorem cancel_injective (h : Injective f) : f x = f y ↔ x = y := by
  refine ⟨fun e => h e, ?_⟩
  intro h
  cases h
  rfl

example (h : Injective f) (h' : f x = f y) : x = y := by
  rw [cancel_injective] at h'
  case _ : Injective f := h
  exact h'

example (h : Injective f) (h' : f x = f y) : x = y := by
  rw [cancel_injective] at h'
  case _ : Injective f
  · exact h
  exact h'

example (hf : Injective f) (hg : Injective g) (h : g (f x) = g (f y)) : x = y := by
  rw [cancel_injective, cancel_injective] at h
  case _ : Injective f | _ : Injective g => assumption
  exact h

example (hf : Injective f) (hg : Injective g) (h : g (f x) = g (f y)) : x = y := by
  rw [cancel_injective, cancel_injective] at h
  repeat case _ : Injective _ => assumption
  exact h

example (hf : Injective f) (hg : Injective g) (h : g (f x) = g (f y)) : x = y := by
  rw [cancel_injective, cancel_injective] at h
  case _ : Injective f | _ : Injective g
  · guard_target = Injective f
    assumption
  · guard_target = Injective g
    assumption
  exact h

example (hf : Injective f) (hg : Injective g) (h : g (f x) = g (f y)) : x = y := by
  rw [cancel_injective, cancel_injective] at h
  case _ : Injective f | _ : Injective g => _
  · guard_target = Injective f
    assumption
  · guard_target = Injective g
    assumption
  exact h

example (a : Nat) : 0 + a = a := by
  induction a
  case _ n ih : 0 + (n + 1) = n + 1 =>
    guard_target =ₛ 0 + (n + 1) = n + 1
    rw [← Nat.add_assoc, ih]
  case _ : 0 + 0 = 0 := rfl

example (a : Nat) : 0 + a = a := by
  induction a
  case _ n ih : 0 + (n + 1) = n + 1 | _ : 0 + 0 = 0
  · rw [← Nat.add_assoc, ih]
  · rfl

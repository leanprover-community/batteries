import Std.Tactic.Case
import Std.Tactic.GuardExpr

set_option linter.missingDocs false

example (h : x = y) (h' : z = w) : x = y ∧ z = w := by
  constructor
  fail_if_success show z = z
  case : z = _
  · exact h'
  exact h

example (h : x = y) (h' : z = w) : x = y ∧ z = w := by
  constructor
  case : z = _ =>
    exact h'
  case left =>
    exact h

example (h : x = y) (h' : z = w) : x = y ∧ z + 0 = w := by
  constructor
  case : z = _ =>
    guard_target =ₛ z = w
    exact h'
  case left =>
    exact h

example (x y z : α) (h : x = y) (h' : y = z) : x = z := by
  apply Eq.trans
  case : α := y
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
  case : Injective f := h
  exact h'

example (h : Injective f) (h' : f x = f y) : x = y := by
  rw [cancel_injective] at h'
  case : Injective f
  · exact h
  exact h'

example (hf : Injective f) (hg : Injective g) (h : g (f x) = g (f y)) : x = y := by
  rw [cancel_injective, cancel_injective] at h
  case : Injective f | Injective g => assumption
  exact h

example (hf : Injective f) (hg : Injective g) (h : g (f x) = g (f y)) : x = y := by
  rw [cancel_injective, cancel_injective] at h
  case : Injective f | Injective g
  · guard_target = Injective f
    assumption
  · guard_target = Injective g
    assumption
  exact h

example (a : Nat) : 0 + a = a := by
  induction a
  case : 0 + (n + 1) = n + 1 with n ih =>
    guard_target =ₛ 0 + (n + 1) = n + 1
    rw [← Nat.add_assoc, ih]
  case : 0 + 0 = 0 := rfl

example (a : Nat) : 0 + a = a := by
  induction a
  case : 0 + (n + 1) = n + 1 with n ih | 0 + 0 = 0
  · rw [← Nat.add_assoc, ih]
  · rfl

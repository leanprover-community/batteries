/-
Copyright (c) 2022 Arthur Paulino. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Paulino, Gabriel Ebner
-/

set_option linter.missingDocs false

example {P : Prop} (p : P) : P := by simpa

example {P : Prop} (p : False) : P := by simp at p

def foo (n : α) := [n]

section unnecessarySimpa

/--
warning: try 'simp' instead of 'simpa'
note: this linter can be disabled with `set_option linter.unnecessarySimpa false`
-/
#guard_msgs in
example : foo n = [n] := by
  simpa only [foo]

/--
warning: try 'simp at h' instead of 'simpa using h'
note: this linter can be disabled with `set_option linter.unnecessarySimpa false`
-/
#guard_msgs in
example (h : foo n ≠ [n]) : False := by
  simpa [foo] using h

end unnecessarySimpa

example (p : Nat → Prop) (h : p (a + b)) : p (b + a) := by
  have : a + b = b + a := Nat.add_comm _ _
  simpa [this] using h

def Injective (f : α → β) : Prop := ∀ ⦃a₁ a₂⦄, f a₁ = f a₂ → a₁ = a₂

namespace div_left_inj_issue

class Inv (α : Type u) where
  inv : α → α

class Group (α) extends Mul α, Div α, Inv α

variable [Group G]

axiom div_eq_mul_inv (a b : G) : a / b = a * Inv.inv b

axiom mul_left_injective (a : G) : Injective (· * a)

theorem div_left_injective (b : G) : Injective fun a => a / b := by
  simpa only [div_eq_mul_inv] using fun a a' h => mul_left_injective (Inv.inv b) h

end div_left_inj_issue

namespace Prod

theorem mk.inj_iff {a₁ a₂ : α} {b₁ b₂ : β} : (a₁, b₁) = (a₂, b₂) ↔ a₁ = a₂ ∧ b₁ = b₂ :=
  Iff.of_eq (mk.injEq _ _ _ _)

theorem mk.inj_left {α β : Type _} (a : α) : Injective (Prod.mk a : β → α × β) := by
  intro b₁ b₂ h
  simpa only [true_and, Prod.mk.inj_iff, eq_self] using h

end Prod

theorem implicit_lambda (h : ∀ {x : Nat}, a = x) : a = 2 := by
  simpa using h

theorem implicit_lambda2 (h : a = 2) : ∀ {x : Nat}, a = 2 := by
  simpa using h

theorem no_implicit_lambda (h : ∀ {x : Nat}, a = x) : ∀ {x : Nat}, a = x := by
  simpa using @h

#guard_msgs (drop warning) in
theorem thm : (a : Int) ≤ b - c ↔ a + b ≤ c := sorry

#guard_msgs (drop warning) in
theorem thm2 : (b : Int) - c ≤ (a - b) - (a - c) := sorry

example : (b - c : Int) + (a - b) + a ≤ c := by
  simpa only [thm] using thm2

example : (b - c : Int) + (a - b) + a ≤ c := by
  simpa only [thm] using @thm2

example (P : Bool) (h : ¬ ¬ P) : P := by
  have : ¬ ¬ P := h
  simpa

/-- info: Try this: simpa only using h -/
#guard_msgs in
example (p : Prop) (h : p) : p := by simpa? using h

/-- info: Try this: simpa only [and_true] using h -/
#guard_msgs in
example (p : Prop) (h : p ∧ True) : p := by simpa? using h

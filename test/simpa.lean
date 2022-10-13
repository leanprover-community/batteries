/-
Copyright (c) 2022 Arthur Paulino. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Paulino, Gabriel Ebner
-/
import Std.Tactic.Simpa

example {P : Prop} (p : P) : P := by simpa

example {P : Prop} (p : P) : P := by simpa using p

def foo (n : α) := [n]

example : foo n = [n] := by
  fail_if_success simpa only [foo]
  simp only [foo]

example (p : Nat → Prop) (h : p (a + b)) : p (b + a) := by
  have : a + b = b + a := Nat.add_comm _ _
  simpa [this] using h

namespace div_left_inj_issue

class Inv (α : Type u) where
  inv : α → α

class Group (α) extends Mul α, Div α, Inv α

variable [Group G]

def injective (f : α → β) : Prop := ∀ ⦃a₁ a₂⦄, f a₁ = f a₂ → a₁ = a₂

axiom div_eq_mul_inv (a b : G) : a / b = a * Inv.inv b

axiom mul_left_injective (a : G) : injective (· * a)

theorem div_left_injective (b : G) : injective fun a => a / b := by
  simpa only [div_eq_mul_inv] using fun a a' h => mul_left_injective (Inv.inv b) h

end div_left_inj_issue

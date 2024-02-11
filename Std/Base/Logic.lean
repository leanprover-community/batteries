/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad, Floris van Doorn, Mario Carneiro
-/

/-# iff -/

@[simp] theorem eq_iff_iff {p q : Prop} : (p = q) ↔ (p ↔ q) :=
  Iff.intro (fun e => Iff.intro e.mp e.mpr) propext

theorem iff_of_true (ha : a) (hb : b) : a ↔ b := ⟨fun _ => hb, fun _ => ha⟩

theorem iff_true_intro (h : a) : a ↔ True := iff_of_true h ⟨⟩

/-# and -/

@[simp] theorem and_not_self : ¬(a ∧ ¬a) | ⟨ha, hn⟩ => hn ha

@[simp] theorem not_and_self : ¬(¬a ∧ a) | ⟨hn, ha⟩ => hn ha

@[simp] theorem and_self_left : a ∧ (a ∧ b) ↔ a ∧ b :=
  ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, h.1, h.2⟩⟩

@[simp] theorem and_self_right : (a ∧ b) ∧ b ↔ a ∧ b :=
  ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, h.2⟩, h.2⟩⟩

/-# or -/

theorem Or.symm : a ∨ b → b ∨ a := .rec .inr .inl

@[simp] theorem or_self_left : a ∨ (a ∨ b) ↔ a ∨ b := ⟨.rec .inl id, .rec .inl (.inr ∘ .inr)⟩

@[simp] theorem or_self_right : (a ∨ b) ∨ b ↔ a ∨ b := ⟨.rec id .inr, .rec (.inl ∘ .inl) .inr⟩

/-# implication -/

@[simp] theorem imp_self : (a → a) ↔ True := iff_true_intro id

@[simp] theorem and_imp : (a ∧ b → c) ↔ (a → b → c) :=
  ⟨fun h ha hb => h ⟨ha, hb⟩, fun h ⟨ha, hb⟩ => h ha hb⟩

/--
This seems sensible as a rule, but in combination with `and_imp`, turns
`(a ∧ b) → c` into `a ∧ ¬b` which is equivalent to `!(a & b)` ~> `a & (!b)`
and simp currently avoids distributing `not` over `and`.
-/
theorem imp_false : (a → False) ↔ ¬a := Iff.rfl

/-# ite -/

/-- Negation of the condition `P : Prop` in a `dite` is the same as swapping the branches. -/
@[simp] theorem dite_not (P : Prop) {_ : Decidable P}  (x : ¬P → α) (y : ¬¬P → α) :
    dite (¬P) x y = dite P (fun h => y (not_not_intro h)) x := by
  by_cases h : P <;> simp [h]

/-- Negation of the condition `P : Prop` in a `ite` is the same as swapping the branches. -/
@[simp] theorem ite_not (P : Prop) {_ : Decidable P} (x y : α) : ite (¬P) x y = ite P y x :=
  dite_not P (fun _ => x) (fun _ => y)

@[simp] theorem ite_true_same (p q : Prop) [Decidable p] : (if p then p else q) = (p ∨ q) := by
  by_cases h : p <;> simp [h]

@[simp] theorem ite_false_same (p q : Prop) [Decidable p] : (if p then q else p) = (p ∧ q) := by
  by_cases h : p <;> simp [h]

/-# Decidable -/

@[simp] theorem decide_eq_false_iff_not (p : Prop) {_ : Decidable p} : (decide p = false) ↔ ¬p :=
  ⟨of_decide_eq_false, decide_eq_false⟩

theorem decide_eq_true_iff (p : Prop) [Decidable p] : (decide p = true) ↔ p := by simp

@[simp] theorem decide_eq_decide {p q : Prop} {_ : Decidable p} {_ : Decidable q} :
    decide p = decide q ↔ (p ↔ q) := by
  apply Iff.intro
  · intro h
    rw [← decide_eq_true_iff p, h, decide_eq_true_iff]
    exact Iff.rfl
  · intro h
    simp [h]

@[simp] theorem Decidable.not_not [Decidable p] : ¬¬p ↔ p := ⟨of_not_not, not_not_intro⟩

namespace Decidable

/-- Simplify p ∨ ¬p -/
@[simp] theorem or_not_self (p : Prop) [Decidable p] : p ∨ ¬p := em p

@[simp] theorem not_or_self (p : Prop) [Decidable p] : ¬p ∨ p := (em p).symm

@[simp]
theorem decide_not (p : Prop) [h : Decidable (p → False)] [g : Decidable p] :
    (@decide (¬p) h) = !(@decide p g) := by
  by_cases h : p <;> simp [h]

@[simp]
theorem decide_and (p q : Prop) [Decidable p] [Decidable q] :
    decide (p ∧ q) = (p && q) := by
  by_cases h : p <;> simp [h]

@[simp]
theorem decide_or (p q : Prop) [Decidable p] [Decidable q] :
    decide (p ∨ q) = (p || q) := by
  by_cases h : p <;> simp [h]

@[simp]
theorem decide_iff (p q : Prop) [Decidable p] [Decidable q] :
    (decide (p ↔ q)) = ((p : Bool) == (q : Bool)) := by
  by_cases g : p <;> by_cases h : q <;> simp [g, h, BEq.beq]

-- From Mathlib
@[simp]
theorem if_true_left_eq_or (p : Prop) [Decidable p] (f : Prop) :
    ite p True f ↔ p ∨ f := by by_cases h : p <;> simp [h]

-- From Mathlib
@[simp]
theorem if_false_left_eq_and (p : Prop) [Decidable p] (f : Prop) :
    ite p False f ↔ ¬p ∧ f := by by_cases h : p <;> simp [h]

-- From Mathlib
@[simp]
theorem if_true_right_eq_or (p : Prop) [Decidable p] (t : Prop) :
    ite p t True ↔ ¬p ∨ t := by by_cases h : p <;> simp [h]

-- From Mathlib
@[simp]
theorem if_false_right_eq_and (p : Prop) [Decidable p] (t : Prop) :
    ite p t False ↔ p ∧ t := by by_cases h : p <;> simp [h]

end Decidable

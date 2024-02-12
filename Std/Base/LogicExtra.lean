import Std.Base.Logic

/-! ## distributivity -/

@[simp]
theorem and_not_or_dist (x y z : Prop) : (x ∧ ¬(y ∨ z)) ↔ (x ∧ (¬y ∧ ¬z)) := by
  rw [not_or]
  exact Iff.refl _

@[simp]
theorem not_or_and_dist (x y z : Prop) : (¬(x ∨ y) ∧ z) ↔ ((¬x ∧ ¬y) ∧ z) := by
  rw [not_or]
  exact Iff.refl _


/-! ## if-then-else -/

@[simp] theorem ite_true_same (p q : Prop) [Decidable p] : (if p then p else q) = (p ∨ q) := by
  by_cases h : p <;> simp [h]

@[simp] theorem ite_false_same (p q : Prop) [Decidable p] : (if p then q else p) = (p ∧ q) := by
  by_cases h : p <;> simp [h]

/-# Decidable -/

namespace Decidable

/-- Prop versions of and -/
@[simp] theorem or_not_self (p : Prop) [Decidable p] : p ∨ ¬p := em p

@[simp] theorem not_or_self (p : Prop) [Decidable p] : ¬p ∨ p := (em p).symm

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


@[simp]
theorem or_not_and_dist (x y z : Prop) [Decidable y] [Decidable z] :
    (x ∨ ¬(y ∧ z)) ↔ (x ∨ (¬y ∨ ¬z)) := by
  rw [Decidable.not_and_iff_or_not]
  exact Iff.refl _

@[simp]
theorem not_and_or_dist (x y z : Prop) [Decidable x] [Decidable y] :
    (¬(x ∧ y) ∨ z) ↔ ((¬x ∨ ¬y) ∨ z) := by
  rw [Decidable.not_and_iff_or_not]
  exact Iff.refl _

end Decidable

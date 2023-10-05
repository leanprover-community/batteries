/-
Copyright (c) 2022 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/

import Std.Logic

/-! ## Boolean equality -/

/-- `PartialEquivBEq α` says that the `BEq` implementation is a
partial equivalence relation, that is:
* it is symmetric: `a == b → b == a`
* it is transitive: `a == b → b == c → a == c`.
-/
class PartialEquivBEq (α) [BEq α] : Prop where
  /-- Symmetry for `BEq`. If `a == b` then `b == a`. -/
  symm : (a : α) == b → b == a
  /-- Transitivity for `BEq`. If `a == b` and `b == c` then `a == c`. -/
  trans : (a : α) == b → b == c → a == c

instance [BEq α] [LawfulBEq α] : PartialEquivBEq α where
  symm h := by rw [beq_iff_eq] at *; rw [h]
  trans h₁ h₂ := by rw [beq_iff_eq] at *; exact h₁.trans h₂

theorem beq_symm [BEq α] [PartialEquivBEq α] {a b : α} : a == b → b == a :=
  PartialEquivBEq.symm

theorem beq_trans [BEq α] [PartialEquivBEq α] {a b c : α} : a == b → b == c → a == c:=
  PartialEquivBEq.trans

theorem bne_symm [BEq α] [PartialEquivBEq α] {a b : α} : a != b → b != a :=
  fun h => Bool.bne_iff_not_beq.mpr fun h' =>
    Bool.bne_iff_not_beq.mp h (beq_symm h')

theorem bne_trans_right [BEq α] [PartialEquivBEq α] {a b c : α} :
    a == b → b != c → a != c :=
  fun h₁ h₂ => Bool.bne_iff_not_beq.mpr fun h₃ =>
    have := beq_trans (beq_symm h₁) h₃
    Bool.bne_iff_not_beq.mp h₂ this

theorem bne_trans_left [BEq α] [PartialEquivBEq α] {a b c : α} :
    a != b → b == c → a != c :=
  fun h₁ h₂ => Bool.bne_iff_not_beq.mpr fun h₃ =>
    have := beq_trans h₃ (beq_symm h₂)
    Bool.bne_iff_not_beq.mp h₁ this

@[simp] theorem beq_eq_false_iff_ne [BEq α] [LawfulBEq α]
    (a b : α) : (a == b) = false ↔ a ≠ b := by
  simp only [Bool.beq_eq_false_iff, bne_iff_ne]

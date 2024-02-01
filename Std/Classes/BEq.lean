/-
Copyright (c) 2022 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/

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

theorem beq_eq_false_iff_ne [BEq α] [LawfulBEq α]
    (a b : α) : (a == b) = false ↔ a ≠ b := by
  rw [ne_eq, ← beq_iff_eq a b]
  cases a == b <;> decide

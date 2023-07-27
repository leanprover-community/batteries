/-
Copyright (c) 2023 F. G. Dorais. No rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: F. G. Dorais
-/

import Std.Tactic.Alias

namespace Bool
variable (x y z : Bool)

instance (p : Bool → Prop) [inst : DecidablePred p] : Decidable (∀ x, p x) :=
  match inst true, inst false with
  | isFalse ht, _ => isFalse fun h => absurd (h _) ht
  | _, isFalse hf => isFalse fun h => absurd (h _) hf
  | isTrue ht, isTrue hf => isTrue fun | true => ht | false => hf

instance (p : Bool → Prop) [inst : DecidablePred p] : Decidable (∃ x, p x) :=
  match inst true, inst false with
  | isTrue ht, _ => isTrue ⟨_, ht⟩
  | _, isTrue hf => isTrue ⟨_, hf⟩
  | isFalse ht, isFalse hf => isFalse fun | ⟨true, h⟩ => absurd h ht | ⟨false, h⟩ => absurd h hf

/-- Convenience truth table tactic -/
local macro "btt " vars:(colGt ident)* : tactic => `(tactic| revert $vars* <;> decide)

/-- Boolean exclusive or -/
abbrev xor : Bool → Bool → Bool := bne

instance : LE Bool := leOfOrd
instance : LT Bool := ltOfOrd
instance : Max Bool := maxOfLe
instance : Min Bool := minOfLe

@[simp] theorem and_not_self_left : (!x && x) = false := by btt x
@[simp] theorem and_not_self_right : (x && !x) = false := by btt x
theorem and_comm : (x && y) = (y && x) := by btt x y
theorem and_left_comm : (x && (y && z)) = (y && (x && z)) := by btt x y z
theorem and_right_comm : ((x && y) && z) = ((x && z) && y) := by btt x y z
theorem and_or_distrib_left : (x && (y || z)) = ((x && y) || (x && z)) := by btt x y z
theorem and_or_distrib_right : ((x || y) && z) = ((x && z) || (y && z)) := by btt x y z
theorem and_xor_distrib_left : (x && xor y z) = xor (x && y) (x && z) := by btt x y z
theorem and_xor_distrib_right : (xor x y && z) = xor (x && z) (y && z) := by btt x y z
@[local simp] theorem and_deMorgan : (!(x && y)) = (!x || !y) := by btt x y
theorem and_eq_true_iff : (x && y) = true ↔ x = true ∧ y = true := by btt x y
theorem and_eq_false_iff : (x && y) = false ↔ x = false ∨ y = false := by btt x y
alias and_false_left := Bool.false_and
alias and_false_right := Bool.and_false
alias and_true_left := Bool.true_and
alias and_true_right := Bool.and_true
alias not_and := Bool.and_deMorgan

@[simp] theorem or_not_self_left : (!x || x) = true := by btt x
@[simp] theorem or_not_self_right : (x || !x) = true := by btt x
theorem or_comm : (x || y) = (y || x) := by btt x y
theorem or_left_comm : (x || (y || z)) = (y || (x || z)) := by btt x y z
theorem or_right_comm : ((x || y) || z) = ((x || z) || y) := by btt x y z
theorem or_and_distrib_left : (x || (y && z)) = ((x || y) && (x || z)) := by btt x y z
theorem or_and_distrib_right : ((x && y) || z) = ((x || z) && (y || z)) := by btt x y z
@[local simp] theorem or_deMorgan : (!(x || y)) = (!x && !y) := by btt x y
theorem or_eq_true_iff : (x || y) = true ↔ x = true ∨ y = true := by btt x y
theorem or_eq_false_iff : (x || y) = false ↔ x = false ∧ y = false := by btt x y
alias or_false_left := Bool.false_or
alias or_false_right := Bool.or_false
alias or_true_left := Bool.true_or
alias or_true_right := Bool.or_true
alias not_or := Bool.or_deMorgan

@[simp] theorem xor_false_left : xor false x = x := by btt x
@[simp] theorem xor_false_right : xor x false = x := by btt x
@[simp] theorem xor_true_left : xor true x = !x := by btt x
@[simp] theorem xor_true_right : xor x true = !x := by btt x
@[simp] theorem xor_not_self_left : xor (!x) x = true := by btt x
@[simp] theorem xor_not_self_right : xor x (!x) = true := by btt x
@[simp] theorem xor_not_left : xor (!x) y = !(xor x y) := by btt x y
@[simp] theorem xor_not_right : xor x (!y) = !(xor x y) := by btt x y
theorem xor_not_not : xor (!x) (!y) = (xor x y) := by btt x y
theorem xor_self : xor x x = false := bne_self_eq_false ..
theorem xor_comm : xor x y = xor y x := by btt x y
theorem xor_left_comm : xor x (xor y z) = xor y (xor x z) := by btt x y z
theorem xor_right_comm : xor (xor x y) z = xor (xor x z) y := by btt x y z
theorem xor_assoc : xor (xor x y) z = xor x (xor y z) := by btt x y z

@[simp] protected theorem le_true : x ≤ true := by btt x
@[simp] protected theorem false_le : false ≤ x := by btt x
@[simp] protected theorem le_refl : x ≤ x := by btt x
@[simp] protected theorem lt_irrefl : ¬ x < x := by btt x
protected theorem le_trans {x y z : Bool} : x ≤ y → y ≤ z → x ≤ z := by btt x y z
protected theorem le_antisymm {x y : Bool} : x ≤ y → y ≤ x → x = y := by btt x y
protected theorem le_total (x y : Bool) : x ≤ y ∨ y ≤ x := by btt x y
protected theorem lt_asymm {x y : Bool} : x < y → ¬ y < x := by btt x y
protected theorem lt_trans {x y z : Bool} : x < y → y < z → x < z := by btt x y z
protected theorem lt_iff_le_not_le {x y : Bool} : x < y ↔ x ≤ y ∧ ¬ y ≤ x := by btt x y
protected theorem lt_of_le_of_lt {x y z : Bool} : x ≤ y → y < z → x < z := by btt x y z
protected theorem lt_of_lt_of_le {x y z : Bool} : x < y → y ≤ z → x < z := by btt x y z
protected theorem le_of_lt {x y : Bool} : x < y → x ≤ y := by btt x y z
protected theorem le_of_eq {x y : Bool} : x = y → x ≤ y := by btt x y z
protected theorem ne_of_lt {x y : Bool} : x < y → x ≠ y := by btt x y z
protected theorem lt_of_le_of_ne {x y : Bool} : x ≤ y → x ≠ y → x < y := by btt x y z
protected theorem le_of_lt_or_eq {x y : Bool} : x < y ∨ x = y → x ≤ y := by btt x y z
protected theorem eq_true_of_true_le {x : Bool} : true ≤ x → x = true := by btt x
protected theorem eq_false_of_le_false {x : Bool} : x ≤ false → x = false := by btt x

protected theorem max_eq_or (x y : Bool) : max x y = (x || y) := by btt x y
protected theorem min_eq_and (x y : Bool) : min x y = (x && y) := by btt x y

theorem not_inj {x y : Bool} : (!x) = (!y) → x = y := by btt x y

theorem not_inj' {x y : Bool} : (!x) = (!y) ↔ x = y := ⟨not_inj, fun | rfl => rfl⟩

theorem and_or_inj_right {m x y : Bool}: (x && m) = (y && m) → (x || m) = (y || m) → x = y := by
  btt m x y

theorem and_or_inj_right' {m x y : Bool}: (x && m) = (y && m) ∧ (x || m) = (y || m) ↔ x = y :=
  ⟨fun ⟨h₁, h₂⟩ => and_or_inj_right h₁ h₂, fun | rfl => ⟨rfl, rfl⟩⟩

theorem and_or_inj_left {m x y : Bool} : (m && x) = (m && y) → (m || x) = (m || y) → x = y := by
  btt m x y

theorem and_or_inj_left' {m x y : Bool} : (m && x) = (m && y) ∧ (m || x) = (m || y) ↔ x = y :=
  ⟨fun ⟨h₁, h₂⟩ => and_or_inj_left h₁ h₂, fun | rfl => ⟨rfl, rfl⟩⟩

end Bool

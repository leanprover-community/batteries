/-
Copyright (c) 2023 F. G. Dorais. All rights reserved.
eleased under Apache 2.0 license as described in the file LICENSE.
Authors: F. G. Dorais
-/

/-- Boolean exclusive or -/
abbrev xor : Bool → Bool → Bool := bne

namespace Bool
variable (x y z : Bool)

/-- Notation for `xor` -/
scoped infixl:30 " ^^ " => xor

/- Boolean truth table tactic -/
local syntax "btt" (&"using" tactic)? (colGt term:max)* : tactic
macro_rules
| `(tactic| btt) => `(tactic| rfl)
| `(tactic| btt using $tac) => `(tactic| $tac)
| `(tactic| btt $[using $tac]? $x:term $xs:term*) =>
  `(tactic| cases ($x : Bool) <;> btt $[using $tac]? $xs*)

instance : LE Bool := leOfOrd
instance : LT Bool := ltOfOrd

theorem not_and : (!(x && y)) = (!x || !y) := by btt x y
theorem not_or : (!(x || y)) = (!x && !y) := by btt x y

@[simp] theorem and_false_left : (false && x) = false := by btt x
@[simp] theorem and_false_right : (x && false) = false := by btt x
@[simp] theorem and_true_left : (true && x) = x := by btt x
@[simp] theorem and_true_right : (x && true) = x := by btt x
@[simp] theorem and_not_self_left : (!x && x) = false := by btt x
@[simp] theorem and_not_self_right : (x && !x) = false := by btt x
@[simp] theorem and_idem : (x && x) = x := by btt x
theorem and_comm : (x && y) = (y && x) := by btt x y
theorem and_left_comm : (x && (y && z)) = (y && (x && z)) := by btt x y z
theorem and_right_comm : ((x && y) && z) = ((x && z) && y) := by btt x y z
theorem and_or_distrib_left : (x && (y || z)) = ((x && y) || (x && z)) := by btt x y z
theorem and_or_distrib_right : ((x || y) && z) = ((x && z) || (y && z)) := by btt x y z
theorem and_xor_distrib_left : (x && (y ^^ z)) = ((x && y) ^^ (x && z)) := by btt x y z
theorem and_xor_distrib_right : ((x ^^ y) && z) = ((x && z) ^^ (y && z)) := by btt x y z
@[local simp] theorem and_deMorgan : (!(x && y)) = (!x || !y) := by btt x y
theorem and_eq_true_iff : (x && y) = true ↔ x = true ∧ y = true := by btt using simp x y
theorem and_eq_false_iff : (x && y) = false ↔ x = false ∨ y = false := by btt using simp x y

@[simp] theorem or_false_left : (false || x) = x := by btt x
@[simp] theorem or_false_right : (x || false) = x := by btt x
@[simp] theorem or_true_left : (true || x) = true := by btt x
@[simp] theorem or_true_right : (x || true) = true := by btt x
@[simp] theorem or_not_self_left : (!x || x) = true := by btt x
@[simp] theorem or_not_self_right : (x || !x) = true := by btt x
@[simp] theorem or_idem : (x || x) = x := by btt x
theorem or_comm : (x || y) = (y || x) := by btt x y
theorem or_left_comm : (x || (y || z)) = (y || (x || z)) := by btt x y z
theorem or_right_comm : ((x || y) || z) = ((x || z) || y) := by btt x y z
theorem or_and_distrib_left : (x || (y && z)) = ((x || y) && (x || z)) := by btt x y z
theorem or_and_distrib_right : ((x && y) || z) = ((x || z) && (y || z)) := by btt x y z
@[local simp] theorem or_deMorgan : (!(x || y)) = (!x && !y) := by btt x y
theorem or_eq_true_iff : (x || y) = true ↔ x = true ∨ y = true := by btt using simp x y
theorem or_eq_false_iff : (x || y) = false ↔ x = false ∧ y = false := by btt using simp x y

@[simp] theorem xor_false_left : (false ^^ x) = x := by btt x
@[simp] theorem xor_false_right : (x ^^ false) = x := by btt x
@[simp] theorem xor_true_left : (true ^^ x) = !x := by btt x
@[simp] theorem xor_true_right : (x ^^ true) = !x := by btt x
@[simp] theorem xor_self : (x ^^ x) = false := by btt x
@[simp] theorem xor_not_self_left : (!x ^^ x) = true := by btt x
@[simp] theorem xor_not_self_right : (x ^^ !x) = true := by btt x
theorem xor_comm : (x ^^ y) = (y ^^ x) := by btt x y
theorem xor_left_comm : (x ^^ (y ^^ z)) = (y ^^ (x ^^ z)) := by btt x y z
theorem xor_right_comm : ((x ^^ y) ^^ z) = ((x ^^ z) ^^ y) := by btt x y z
theorem xor_assoc : ((x ^^ y) ^^ z) = (x ^^ (y ^^ z)) := by btt x y z

attribute [local simp] and_assoc or_assoc xor_assoc

/-- Boolean equal -/
protected abbrev beq := x == y
/-- Boolean nonequal -/
protected abbrev bne := x != y
/-- Boolean greater-or-equal -/
protected abbrev bge := x || !y
/-- Boolean greater-than -/
protected abbrev bgt := x && !y
/-- Boolean less-or-equal -/
protected abbrev ble := !x || y
/-- Boolean less-than -/
protected abbrev blt := !x && y

theorem beq_eq_decide_eq : Bool.beq x y = decide (x = y) := by btt x y
theorem bne_eq_decide_ne : Bool.bne x y = decide (x ≠ y) := by btt x y
theorem bge_eq_decide_ge : Bool.bge x y = decide (x ≥ y) := by btt x y
theorem bgt_eq_decide_gt : Bool.bgt x y = decide (x > y) := by btt x y
theorem ble_eq_decide_le : Bool.ble x y = decide (x ≤ y) := by btt x y
theorem blt_eq_decide_lt : Bool.blt x y = decide (x < y) := by btt x y

protected theorem le_refl : x ≤ x := by btt x
protected theorem le_trans {x y z : Bool} : x ≤ y → y ≤ z → x ≤ z := by btt using simp x y z
protected theorem le_antisymm {x y : Bool} : x ≤ y → y ≤ x → x = y := by btt using simp x y
protected theorem lt_irrefl : ¬ x < x := by btt using simp x
protected theorem lt_asymm {x y : Bool} : x < y → ¬ y < x := by btt using simp x y
protected theorem lt_trans {x y z : Bool} : x < y → y < z → x < z := by btt using simp x y z
protected theorem lt_of_le_of_lt {x y z : Bool} : x ≤ y → y < z → x < z := by btt using simp x y z
protected theorem lt_of_lt_of_le {x y z : Bool} : x < y → y ≤ z → x < z := by btt using simp x y z
protected theorem le_of_lt {x y : Bool} : x < y → x ≤ y := by btt using simp x y z
protected theorem le_of_eq {x y : Bool} : x = y → x ≤ y := by btt using simp x y z
protected theorem ne_of_lt {x y : Bool} : x < y → x ≠ y := by btt using simp x y z
protected theorem lt_of_le_of_ne {x y : Bool} : x ≤ y → x ≠ y → x < y := by btt using simp x y z
protected theorem le_of_lt_or_eq {x y : Bool} : x < y ∨ x = y → x ≤ y := by btt using simp x y z
protected theorem le_true : x ≤ true := by btt x
protected theorem false_le : false ≤ x := by btt x
protected theorem eq_true_of_true_le {x : Bool} : true ≤ x → x = true := by btt using simp x
protected theorem eq_false_of_le_false {x : Bool} : x ≤ false → x = false := by btt using simp x

theorem not_inj {x y : Bool} : (!x) = (!y) → x = y := by btt using simp x y

theorem not_inj' {x y : Bool} : (!x) = (!y) ↔ x = y := ⟨not_inj, fun | rfl => rfl⟩

theorem and_or_inj_right {m x y : Bool}: (x && m) = (y && m) → (x || m) = (y || m) → x = y := by
  btt using simp m x y

theorem and_or_inj_right' {m x y : Bool}: (x && m) = (y && m) ∧ (x || m) = (y || m) ↔ x = y :=
  ⟨fun ⟨h₁, h₂⟩ => and_or_inj_right h₁ h₂, fun | rfl => ⟨rfl, rfl⟩⟩

theorem and_or_inj_left {m x y : Bool} : (m && x) = (m && y) → (m || x) = (m || y) → x = y := by
  btt using simp m x y

theorem and_or_inj_left' {m x y : Bool} : (m && x) = (m && y) ∧ (m || x) = (m || y) ↔ x = y :=
  ⟨fun ⟨h₁, h₂⟩ => and_or_inj_left h₁ h₂, fun | rfl => ⟨rfl, rfl⟩⟩

section
variable (xs ys : List Bool)

attribute [local simp] List.map List.join

/-- Boolean conjunction (`and`) of a list -/
abbrev all : Bool := xs.all id

@[simp] theorem all_nil : all [] = true := rfl
@[simp] theorem all_one : all [x] = x := Bool.and_true x
@[local simp] theorem all_cons  : all (x :: xs) = (x && all xs) := rfl

@[local simp] theorem all_append : all (xs ++ ys) = (all xs && all ys) := by
  induction xs with
  | nil => simp
  | cons _ _ ih => simp [ih]

theorem all_join (xss : List (List Bool)) : all (xss.map all) = all xss.join := by
  induction xss with
  | nil => rfl
  | cons _ _ ih => simp [ih]

/-- Boolean disjunction (`or`) of a list -/
abbrev any : Bool := xs.any id

@[simp] theorem any_nil : any [] = false := rfl
@[simp] theorem any_one : any [x] = x := Bool.or_false x
@[local simp] theorem any_cons : any (x :: xs) = (x || any xs) := rfl

@[local simp] theorem any_append : any (xs ++ ys) = (any xs || any ys) := by
  induction xs with
  | nil => simp
  | cons _ _ ih => simp [ih]

theorem any_join (xss : List (List Bool)) : any (xss.map any) = any xss.join := by
  induction xss with
  | nil => rfl
  | cons _ _ ih => simp [ih]

theorem all_deMorgan : (!all xs) = any (xs.map (!·)) := by
  induction xs with
  | nil => rfl
  | cons _ _ ih => simp [ih]

theorem any_deMorgan : (!any xs) = all (xs.map (!·)) := by
  induction xs with
  | nil => rfl
  | cons _ _ ih => simp [ih]

end

end Bool

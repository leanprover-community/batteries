/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg, François G. Dorais
-/
import Std.Tactic.BVDecide
import Batteries.Data.UInt
import Batteries.Tactic.Basic

namespace Char

theorem le_antisymm_iff {x y : Char} : x = y ↔ x ≤ y ∧ y ≤ x :=
  Char.ext_iff.trans UInt32.le_antisymm_iff

instance : Batteries.LawfulOrd Char := .compareOfLessAndEq
  (fun _ => Nat.lt_irrefl _) Nat.lt_trans Nat.not_lt Char.le_antisymm

@[simp] theorem toNat_val (c : Char) : c.val.toNat = c.toNat := rfl

@[simp] theorem toNat_ofNatAux {n : Nat} (h : n.isValidChar) : toNat (ofNatAux n h) = n := by
  simp [ofNatAux, toNat]

theorem toNat_ofNat (n : Nat) : toNat (ofNat n) = if n.isValidChar then n else 0 := by
  split
  · simp [ofNat, *]
  · simp [ofNat, toNat, *]

/-! ## Lemmas for ASCII-casing

These facts apply for ASCII characters only. Recall that `isAlpha`, `isLower`, `isUpper`, `toLower`,
`toUpper` do not consider characters outside the ASCII character range (code points less than 128).
-/

theorem not_isLower_of_isUpper {c : Char} : c.isUpper → ¬ c.isLower := by
  simp only [isUpper, ge_iff_le, UInt32.le_iff_toNat_le, UInt32.reduceToNat, toNat_val,
    Bool.and_eq_true, decide_eq_true_eq, isLower, not_and, Nat.not_le, and_imp]
  omega

theorem not_isUpper_of_isLower {c : Char} : c.isLower → ¬ c.isUpper := by
  simp only [isUpper, ge_iff_le, UInt32.le_iff_toNat_le, UInt32.reduceToNat, toNat_val,
    Bool.and_eq_true, decide_eq_true_eq, isLower, not_and, Nat.not_le, and_imp]
  omega

theorem toLower_eq_of_not_isUpper {c : Char} (h : ¬ c.isUpper) : c.toLower = c := by
  simp only [isUpper, ge_iff_le, Bool.and_eq_true, decide_eq_true_eq, not_and] at h
  simp only [toLower, ge_iff_le, ite_eq_right_iff, and_imp]
  intro h65 h90
  absurd h h65
  exact h90

theorem toLower_eq_of_isUpper {c : Char} (h : c.isUpper) : c.toLower = ofNat (c.toNat + 32) := by
  simp only [isUpper, ge_iff_le, Bool.and_eq_true, decide_eq_true_eq] at h
  simp only [toLower, ge_iff_le, ite_eq_left_iff]
  intro; contradiction

theorem toUpper_eq_of_not_isLower {c : Char} (h : ¬ c.isLower) : c.toUpper = c := by
  simp only [isLower, ge_iff_le, Bool.and_eq_true, decide_eq_true_eq, not_and] at h
  simp only [toUpper, ge_iff_le, ite_eq_right_iff, and_imp]
  intro h97 h122
  absurd h h97
  exact h122

theorem toUpper_eq_of_isLower {c : Char} (h : c.isLower) : c.toUpper = ofNat (c.toNat - 32) := by
  simp only [isLower, ge_iff_le, Bool.and_eq_true, decide_eq_true_eq] at h
  simp only [toUpper, ge_iff_le, ite_eq_left_iff]
  intro; contradiction

@[simp] theorem isUpper_toLower_eq_false (c : Char) : c.toLower.isUpper = false := by
  simp only [isUpper, toLower, ge_iff_le, UInt32.le_iff_toNat_le, UInt32.reduceToNat, toNat_val,
    Bool.and_eq_false_imp, decide_eq_true_eq, decide_eq_false_iff_not, Nat.not_le]
  intro h
  split at h
  · next h' =>
    rw [if_pos h']
    have : (c.toNat + 32).isValidChar := by omega
    simp only [toNat_ofNat, ↓reduceIte, gt_iff_lt, *]
    omega
  · next h' =>
    rw [if_neg h']
    omega

@[simp] theorem isLower_toUpper_eq_false (c : Char) : c.toUpper.isLower = false := by
  simp only [isLower, toUpper, ge_iff_le, UInt32.le_iff_toNat_le, UInt32.reduceToNat, toNat_val,
    Bool.and_eq_false_imp, decide_eq_true_eq, decide_eq_false_iff_not, Nat.not_le]
  intro h
  split at h
  · next h' =>
    rw [if_pos h']
    have : (c.toNat - 32).isValidChar := by omega
    simp [toNat_ofNat, *] at h ⊢
    omega
  · next h' =>
    rw [if_neg h']
    omega

@[simp] theorem isLower_toLower_eq_isAlpha (c : Char) : c.toLower.isLower = c.isAlpha := by
  rw [Bool.eq_iff_iff]
  by_cases h : c.isUpper
  · simp only [isLower, h, toLower_eq_of_isUpper, ge_iff_le, UInt32.le_iff_toNat_le,
      UInt32.reduceToNat, toNat_val, Bool.and_eq_true, decide_eq_true_eq, isAlpha, Bool.true_or,
      iff_true]
    simp only [isUpper, ge_iff_le, UInt32.le_iff_toNat_le, UInt32.reduceToNat, toNat_val,
      Bool.and_eq_true, decide_eq_true_eq] at h
    have : (c.toNat + 32).isValidChar := by omega
    simp [toNat_ofNat, *]
  · simp [toLower_eq_of_not_isUpper, isAlpha, h]

@[simp] theorem isUpper_toUpper_eq_isAlpha (c : Char) : c.toUpper.isUpper = c.isAlpha := by
  rw [Bool.eq_iff_iff]
  by_cases h : c.isLower
  · simp only [isUpper, h, toUpper_eq_of_isLower, ge_iff_le, UInt32.le_iff_toNat_le,
      UInt32.reduceToNat, toNat_val, Bool.and_eq_true, decide_eq_true_eq, isAlpha, Bool.or_true,
      iff_true]
    simp only [isLower, ge_iff_le, UInt32.le_iff_toNat_le, UInt32.reduceToNat, toNat_val,
      Bool.and_eq_true, decide_eq_true_eq] at h
    have : (c.toNat - 32).isValidChar := by omega
    have : 32 ≤ c.toNat := by omega
    simp [toNat_ofNat, Nat.le_sub_iff_add_le, *]
  · simp [toUpper_eq_of_not_isLower, isAlpha, h]

@[simp] theorem isAlpha_toLower_eq_isAlpha (c : Char) : c.toLower.isAlpha = c.isAlpha := by
  simp [isAlpha]

@[simp] theorem isAlpha_toUpper_eq_isAlpha (c : Char) : c.toUpper.isAlpha = c.isAlpha := by
  simp [isAlpha]

@[simp] theorem toLower_toLower_eq_toLower (c : Char) : c.toLower.toLower = c.toLower := by
  simp [toLower_eq_of_not_isUpper]

@[simp] theorem toLower_toUpper_eq_toLower (c : Char) : c.toUpper.toLower = c.toLower := by
  by_cases hl : c.isLower
  · have hu : ¬ c.isUpper := not_isUpper_of_isLower hl
    have hu' : c.toUpper.isUpper := by simp [isAlpha, hl]
    have hv : (c.toNat - 32).isValidChar := by
      simp only [isLower, ge_iff_le, UInt32.le_iff_toNat_le, UInt32.reduceToNat, toNat_val,
        Bool.and_eq_true, decide_eq_true_eq, isUpper, not_and, Nat.not_le] at hl hu
      omega
    have h : 32 ≤ c.toNat := by
      simp only [isLower, ge_iff_le, UInt32.le_iff_toNat_le, UInt32.reduceToNat, toNat_val,
        Bool.and_eq_true, decide_eq_true_eq, isUpper, not_and, Nat.not_le] at hl hu
      omega
    rw [toLower_eq_of_isUpper hu', toUpper_eq_of_isLower hl, toLower_eq_of_not_isUpper hu,
      toNat_ofNat, if_pos hv, Nat.sub_add_cancel h, ofNat_toNat]
  · rw [toUpper_eq_of_not_isLower hl]

@[simp] theorem toUpper_toUpper_eq_toUpper (c : Char) : c.toUpper.toUpper = c.toUpper := by
  simp [toUpper_eq_of_not_isLower]

@[simp] theorem toUpper_toLower_eq_toUpper (c : Char) : c.toLower.toUpper = c.toUpper := by
  by_cases hu : c.isUpper
  · have hl : ¬ c.isLower := not_isLower_of_isUpper hu
    have hl' : c.toLower.isLower := by simp [isAlpha, hu]
    have hv : (c.toNat + 32).isValidChar := by
      simp only [isUpper, ge_iff_le, UInt32.le_iff_toNat_le, UInt32.reduceToNat, toNat_val,
        Bool.and_eq_true, decide_eq_true_eq, isLower, not_and, Nat.not_le] at hu hl
      omega
    rw [toUpper_eq_of_isLower hl', toLower_eq_of_isUpper hu, toUpper_eq_of_not_isLower hl,
      toNat_ofNat, if_pos hv, Nat.add_sub_cancel, ofNat_toNat]
  · rw [toLower_eq_of_not_isUpper hu]

/-- Case folding for ASCII characters only.

Alphabetic ASCII characters are mapped to their lowercase form, all other characters are left
unchanged. This agrees with the Unicode case folding algorithm for ASCII characters.

```
#eval caseFoldAsciiOnly 'A' == 'a'
#eval caseFoldAsciiOnly 'a' == 'a'
#eval caseFoldAsciiOnly 'À' == 'À'
#eval caseFoldAsciiOnly 'à' == 'à'
#eval caseFoldAsciiOnly '$' == '$'
```
-/
abbrev caseFoldAsciiOnly := Char.toLower

theorem isAlpha_iff_isUpper_or_isLower {c : Char} : c.isAlpha ↔ c.isUpper ∨ c.isLower := by
  simp [Char.isAlpha]

theorem toLower_eq_of_isLower {c : Char} : c.isLower → c.toLower = c := by
  simp only [isLower, ge_iff_le, Bool.and_eq_true, decide_eq_true_eq, toLower, ite_eq_right_iff,
    and_imp]
  intro h0 _ _ h3
  have _ : 97 ≤ c.val.toNat ∧ c.val.toNat ≤ 90 := ⟨h0, h3⟩
  omega

theorem toLower_eq_of_not_isAlpha {c : Char} : ¬c.isAlpha → c.toLower = c := by
  simp only [isAlpha, isUpper, ge_iff_le, isLower, Bool.or_eq_true, Bool.and_eq_true,
    decide_eq_true_eq, not_or, not_and, UInt32.not_le, toLower, ite_eq_right_iff, and_imp]
  intro h0 _ h2 h3
  have _ : c.val.toNat ≤ 90 ∧ 90 < c.val.toNat:= ⟨h3, h0 h2⟩
  omega

/--
Bool-valued comparison of two `Char`s for *ASCII*-case insensitive equality.

```
#eval beqCaseInsensitiveAsciiOnly 'a' 'A' -- true
#eval beqCaseInsensitiveAsciiOnly 'a' 'a' -- true
#eval beqCaseInsensitiveAsciiOnly '$' '$' -- true
#eval beqCaseInsensitiveAsciiOnly 'a' 'b' -- false
#eval beqCaseInsensitiveAsciiOnly 'γ' 'Γ' -- false
#eval beqCaseInsensitiveAsciiOnly 'ä' 'Ä' -- false
```
-/
def beqCaseInsensitiveAsciiOnly (c₁ c₂ : Char) : Bool := c₁.toLower == c₂.toLower

theorem beqCaseInsensitiveAsciiOnly.eqv : Equivalence (beqCaseInsensitiveAsciiOnly · ·) := {
  refl _ := BEq.rfl
  trans _ _ := by simp_all [beqCaseInsensitiveAsciiOnly]
  symm := by simp_all [beqCaseInsensitiveAsciiOnly]}

/--
Setoid structure on `Char` using `beqCaseInsensitiveAsciiOnly`
-/
def beqCaseInsensitiveAsciiOnly.isSetoid : Setoid Char:=
  ⟨(beqCaseInsensitiveAsciiOnly · ·), beqCaseInsensitiveAsciiOnly.eqv⟩

/--
ASCII-case insensitive implementation comparison returning an `Ordering`. Useful for sorting.

```
#eval cmpCaseInsensitiveAsciiOnly 'a' 'A' -- eq
#eval cmpCaseInsensitiveAsciiOnly 'a' 'a' -- eq
#eval cmpCaseInsensitiveAsciiOnly '$' '$' -- eq
#eval cmpCaseInsensitiveAsciiOnly 'a' 'b' -- lt
#eval cmpCaseInsensitiveAsciiOnly 'γ' 'Γ' -- gt
#eval cmpCaseInsensitiveAsciiOnly 'ä' 'Ä' -- gt
```
-/
def cmpCaseInsensitiveAsciiOnly (c₁ c₂ : Char) : Ordering := Ord.compare c₁.toLower c₂.toLower

/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/
import Std.Tactic.BVDecide
import Batteries.Data.UInt
import Batteries.Tactic.Alias

theorem Char.le_antisymm_iff {x y : Char} : x = y ↔ x ≤ y ∧ y ≤ x :=
  Char.ext_iff.trans UInt32.le_antisymm_iff

instance : Batteries.LawfulOrd Char := .compareOfLessAndEq
  (fun _ => Nat.lt_irrefl _) Nat.lt_trans Nat.not_lt Char.le_antisymm

namespace Char

/--
Unicode defines a "case folding" algorithm in which upper-case ASCII characters are
mapped onto their lower-case counterparts.

This abbrev standardizes on one direction (it answers the question of whether
one should choose e.g. `toUpper` or `toLower` with respect to case insensitive logic).
-/
abbrev asciiCaseFold := Char.toLower

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

theorem isAlpha_toLower_iff_isAlpha {c : Char} : c.toLower.isAlpha ↔ c.isAlpha := by
  have isUpper_def : c.isUpper → 65 ≤ c.val ∧ c.val ≤ 90 := by
    simp only [isUpper, ge_iff_le, Bool.and_eq_true, decide_eq_true_eq, and_imp]; exact .intro
  apply Iff.intro
  case _ =>
    by_cases hIsAlpha : c.isAlpha
    . intro _; assumption
    . rw [toLower_eq_of_not_isAlpha hIsAlpha]; exact id
  case _ =>
    rw [isAlpha_iff_isUpper_or_isLower]
    rintro (_ | _)
    .
      have hl : 65 ≤ c.val.toNat ∧ c.val.toNat ≤ 90 := isUpper_def ‹_›
      have hValid : (c.val.toNat + 32).isValidChar := by omega
      simp [Char.isAlpha, Char.toLower, Char.isLower, Char.toNat, Char.ofNat,
        Char.ofNatAux, hValid, UInt32.le_iff_toBitVec_le, hl]
      bv_decide
    .
      rw [toLower_eq_of_isLower ‹_›]
      exact isAlpha_iff_isUpper_or_isLower.mpr (.inr ‹_›)

/--
Bool-valued comparison of two `Char`s for *ASCII*-case insensitive equality.
-/
def beqInsensitiveAsciiCase (c₁ c₂ : Char) : Bool := c₁.toLower == c₂.toLower

theorem beqInsensitiveAsciiCase.eqv : Equivalence (beqInsensitiveAsciiCase · ·) := {
  refl _ := BEq.rfl
  trans _ _ := by simp_all [beqInsensitiveAsciiCase]
  symm := by simp_all [beqInsensitiveAsciiCase]}

/--
Setoid structure on `Char` using `beqInsensitiveAsciiCase`
-/
def beqInsensitiveAsciiCase.isSetoid : Setoid Char:=
  ⟨(beqInsensitiveAsciiCase · ·), beqInsensitiveAsciiCase.eqv⟩

/--
ASCII-case insensitive implementation comparison returning an `Ordering`. Useful for sorting.
-/
def cmpInsensitiveAsciiCase (c₁ c₂ : Char) : Ordering := Ord.compare c₁.toLower c₂.toLower

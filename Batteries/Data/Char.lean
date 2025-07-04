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

theorem isUpper_or_isLower_iff_isAlpha {c : Char} : c.isUpper ∨ c.isLower ↔ c.isAlpha := by
  simp [Char.isAlpha]

theorem toLower_eq_of_isLower (c : Char) : c.isLower → c.toLower = c := by
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

theorem toLowerIsAlpha_iff_isAlpha {c : Char} : c.isAlpha ↔ c.toLower.isAlpha := by
  have isUpper_def : c.isUpper → 65 ≤ c.val ∧ c.val ≤ 90 := by
    simp only [isUpper, ge_iff_le, Bool.and_eq_true, decide_eq_true_eq, and_imp]; exact .intro
  apply Iff.intro
  case _ =>
    rw [← isUpper_or_isLower_iff_isAlpha]
    rintro (_ | _)
    .
      have hl : 65 ≤ c.val.toNat ∧ c.val.toNat ≤ 90 := isUpper_def ‹_›
      have hValid : (c.val.toNat + 32).isValidChar := by omega
      simp [Char.isAlpha, Char.toLower, Char.isLower, Char.toNat, Char.ofNat,
        Char.ofNatAux, hValid, UInt32.le_iff_toBitVec_le, hl]
      bv_decide
    .
      rw [toLower_eq_of_isLower c ‹_›]
      exact isUpper_or_isLower_iff_isAlpha.mp (.inr ‹_›)
  case _ =>
    by_cases hIsAlpha : c.isAlpha
    . intro _; assumption
    . rw [toLower_eq_of_not_isAlpha hIsAlpha]; exact id

/--
Prop-valued comparison of two `Char`s for *ascii*-case insensitive equality.
-/
def eqIgnoreAsciiCase (c₁ c₂ : Char) : Prop := c₁.toLower = c₂.toLower

/--
Bool-valued comparison of two `Char`s for *ascii*-case insensitive equality.
-/
def beqIgnoreAsciiCase (c₁ c₂ : Char) : Bool := c₁.toLower == c₂.toLower

theorem eqIgnoreAsciiCase_iff_beqIgnoreAsciiCase (c₁ c₂ : Char) :
  c₁.eqIgnoreAsciiCase c₂ ↔ (c₁.beqIgnoreAsciiCase c₂ = true) := by
  simp [eqIgnoreAsciiCase, beqIgnoreAsciiCase]

theorem eqIgnoreAsciiCase.eqv : Equivalence eqIgnoreAsciiCase := {
  refl _ := rfl
  trans := fun h1 h2 => by simp only [eqIgnoreAsciiCase]; exact h1 ▸ h2
  symm := by simp [eqIgnoreAsciiCase]; exact Eq.symm
}

instance eqIgnoreAsciiCase.isSetoid : Setoid Char:= .mk eqIgnoreAsciiCase eqIgnoreAsciiCase.eqv

end Char

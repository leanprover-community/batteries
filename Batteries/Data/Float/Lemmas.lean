/-
Copyright (c) 2025 Robin Arnez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Arnez
-/
import Batteries.Data.Float.Axioms

theorem Float.toBits_inj {x y : Float} : x.toBits = y.toBits ↔ x = y := by
  constructor
  · intro h
    rw [← Float.ofBits_toBits x, ← Float.ofBits_toBits y, h]
  · rintro rfl
    rfl

example : (2047 <<< 52 ||| 2251799813685248) >>> 52 &&& 2047 = 2047 := by
  simp

theorem Float.toBits_ofBits_of_isNaNBits {x : UInt64} (h : isNaNBits x) :
    (ofBits x).toBits = 0x7ff8_0000_0000_0000 := by
  simp only [toBits_ofBits, h, reduceIte]

theorem Float.toBits_ofBits_of_not_isNaNBits {x : UInt64} (h : isNaNBits x = false) :
    (ofBits x).toBits = x := by
  simp only [toBits_ofBits, h, reduceIte, reduceCtorEq]

@[simp]
theorem Float.toBits_nan : nan.toBits = 0x7ff8_0000_0000_0000 := by
  simp [nan, fromParts, toBits_ofBits_of_isNaNBits, isNaNBits, ← UInt64.toNat_inj]

@[simp]
theorem Float.isNaN_nan : nan.isNaN := by
  rw [isNaN, Float.toBits_nan]; rfl

theorem Float.isNaN_iff_eq_nan (x : Float) : x.isNaN ↔ x = nan := by
  unfold isNaN
  constructor
  · intro h
    rw [← Float.ofBits_toBits x]
    rw [← Float.toBits_inj, Float.toBits_ofBits]
    simp only [h, reduceIte, Float.toBits_nan]
  · intro h
    rw [h, Float.toBits_nan]
    rfl

theorem Float.neg_def (x : Float) : -x = x.neg := rfl

@[simp]
theorem Float.neg_nan : -nan = nan := by
  rw [Float.neg_def, neg, toBits_nan]
  rw [← Float.isNaN_iff_eq_nan, isNaN, toBits_ofBits]
  simp [isNaNBits, ← UInt64.toNat_inj]

protected theorem Float.neg_neg (x : Float) : -(-x) = x := by
  by_cases h : x = nan
  · rw [h, neg_nan, neg_nan]
  · simp only [Float.neg_def, Float.neg]
    rw [toBits_ofBits_of_not_isNaNBits, ← Float.toBits_inj, toBits_ofBits_of_not_isNaNBits]
    · simp only [← UInt64.toNat_inj, UInt64.toNat_xor, UInt64.reduceToNat]
      rw [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
    repeat
    · rw [← Float.isNaN_iff_eq_nan, isNaN] at h
      simpa [isNaNBits, ← UInt64.toNat_inj, Nat.shiftRight_xor_distrib,
        Nat.and_xor_distrib_right] using h

theorem Float.neg_eq_nan_iff {x : Float} : -x = nan ↔ x = nan := by
  constructor
  · intro h
    rw [← Float.neg_neg x, h, neg_nan]
  · intro h
    rw [h, neg_nan]

theorem Float.exponentPart_neg (x : Float) : (-x).exponentPart = x.exponentPart := by
  by_cases h : x = nan
  · rw [h, neg_nan]
  · rw [neg_def, neg, exponentPart, exponentPart]
    rw [toBits_ofBits_of_not_isNaNBits]
    · simp [← UInt64.toNat_inj, Nat.shiftRight_xor_distrib, Nat.and_xor_distrib_right]
    · rw [← Float.isNaN_iff_eq_nan, isNaN] at h
      simpa [isNaNBits, ← UInt64.toNat_inj, Nat.shiftRight_xor_distrib,
        Nat.and_xor_distrib_right] using h

theorem Float.mantissa_neg (x : Float) : (-x).mantissa = x.mantissa := by
  by_cases h : x = nan
  · rw [h, neg_nan]
  · rw [neg_def, neg, mantissa, mantissa]
    rw [toBits_ofBits_of_not_isNaNBits]
    · simp [← UInt64.toNat_inj, Nat.and_xor_distrib_right]
    · rw [← Float.isNaN_iff_eq_nan, isNaN] at h
      simpa [isNaNBits, ← UInt64.toNat_inj, Nat.shiftRight_xor_distrib,
        Nat.and_xor_distrib_right] using h

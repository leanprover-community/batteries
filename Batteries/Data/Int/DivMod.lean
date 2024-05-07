/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Mario Carneiro
-/
import Batteries.Data.Int.Order

/-!
# Lemmas about integer division
-/


open Nat

namespace Int

/-!
### The following lemmas have been commented out here for a while, and need restoration.
-/

/-
theorem eq_mul_ediv_of_mul_eq_mul_of_dvd_left {a b c d : Int}
    (hb : b ≠ 0) (hbc : b ∣ c) (h : b * a = c * d) : a = c / b * d := by
  rcases hbc with ⟨k, hk⟩
  subst hk
  rw [Int.mul_ediv_cancel_left _ hb]
  rw [Int.mul_assoc] at h
  apply mul_left_cancel₀ hb h

/-- If an integer with larger absolute value divides an integer, it is
zero. -/
theorem eq_zero_of_dvd_ofNatAbs_lt_natAbs {a b : Int} (w : a ∣ b) (h : natAbs b < natAbs a) :
    b = 0 := by
  rw [← natAbs_dvd, ← dvd_natAbs, ofNat_dvd] at w
  rw [← natAbs_eq_zero]
  exact eq_zero_of_dvd_of_lt w h

theorem eq_zero_of_dvd_of_nonneg_of_lt {a b : Int} (w₁ : 0 ≤ a) (w₂ : a < b) (h : b ∣ a) : a = 0 :=
  eq_zero_of_dvd_ofNatAbs_lt_natAbs h (natAbs_lt_natAbs_of_nonneg_of_lt w₁ w₂)

/-- If two integers are congruent to a sufficiently large modulus,
they are equal. -/
theorem eq_of_mod_eq_ofNatAbs_sub_lt_natAbs {a b c : Int}
    (h1 : a % b = c) (h2 : natAbs (a - c) < natAbs b) : a = c :=
  Int.eq_of_sub_eq_zero (eq_zero_of_dvd_ofNatAbs_lt_natAbs (dvd_sub_of_emod_eq h1) h2)

theorem ofNat_add_negSucc_of_lt {m n : Nat} (h : m < n.succ) : ofNat m + -[n+1] = -[n+1 - m] := by
  change subNatNat _ _ = _
  have h' : n.succ - m = (n - m).succ
  apply succ_sub
  apply le_of_lt_succ h
  simp [*, subNatNat]

theorem ofNat_add_negSucc_of_ge {m n : Nat} (h : n.succ ≤ m) :
    ofNat m + -[n+1] = ofNat (m - n.succ) := by
  change subNatNat _ _ = _
  have h' : n.succ - m = 0
  apply tsub_eq_zero_iff_le.mpr h
  simp [*, subNatNat]

@[simp]
theorem neg_add_neg (m n : Nat) : -[m+1] + -[n+1] = -[Nat+1.succ (m + n)] :=
  rfl

theorem natAbs_le_of_dvd_ne_zero {s t : Int} (hst : s ∣ t) (ht : t ≠ 0) : natAbs s ≤ natAbs t :=
  not_lt.mp (mt (eq_zero_of_dvd_ofNatAbs_lt_natAbs hst) ht)

theorem natAbs_eq_of_dvd_dvd {s t : Int} (hst : s ∣ t) (hts : t ∣ s) : natAbs s = natAbs t :=
  Nat.dvd_antisymm (natAbs_dvd_iff_dvd.mpr hst) (natAbs_dvd_iff_dvd.mpr hts)

theorem div_dvd_of_dvd {s t : Int} (hst : s ∣ t) : t / s ∣ t := by
  rcases eq_or_ne s 0 with (rfl | hs)
  · simpa using hst
  rcases hst with ⟨c, hc⟩
  simp [hc, Int.mul_div_cancel_left _ hs]

theorem dvd_div_of_mul_dvd {a b c : Int} (h : a * b ∣ c) : b ∣ c / a := by
  rcases eq_or_ne a 0 with (rfl | ha)
  · simp only [Int.div_zero, dvd_zero]

  rcases h with ⟨d, rfl⟩
  refine' ⟨d, _⟩
  rw [mul_assoc, Int.mul_div_cancel_left _ ha]
-/

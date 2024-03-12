/-
Copyright (c) 2023 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Std.Data.Int.DivMod

/-!
# Results about `Int.gcd`.
-/

namespace Int

theorem gcd_dvd_left {a b : Int} : (gcd a b : Int) ∣ a := by
  have := Nat.gcd_dvd_left a.natAbs b.natAbs
  rw [← Int.ofNat_dvd] at this
  exact Int.dvd_trans this natAbs_dvd_self

theorem gcd_dvd_right {a b : Int} : (gcd a b : Int) ∣ b := by
  have := Nat.gcd_dvd_right a.natAbs b.natAbs
  rw [← Int.ofNat_dvd] at this
  exact Int.dvd_trans this natAbs_dvd_self

@[simp] theorem one_gcd {a : Int} : gcd 1 a = 1 := by simp [gcd]
@[simp] theorem gcd_one {a : Int} : gcd a 1 = 1 := by simp [gcd]

@[simp] theorem neg_gcd {a b : Int} : gcd (-a) b = gcd a b := by simp [gcd]
@[simp] theorem gcd_neg {a b : Int} : gcd a (-b) = gcd a b := by simp [gcd]

/-- Computes the least common multiple of two integers, as a `Nat`. -/
def lcm (m n : Int) : Nat := m.natAbs.lcm n.natAbs

theorem lcm_ne_zero (hm : m ≠ 0) (hn : n ≠ 0) : lcm m n ≠ 0 := by
  simp only [lcm]
  apply Nat.lcm_ne_zero <;> simpa

theorem dvd_lcm_left {a b : Int} : a ∣ lcm a b :=
  Int.dvd_trans dvd_natAbs_self (Int.ofNat_dvd.mpr (Nat.dvd_lcm_left a.natAbs b.natAbs))

theorem dvd_lcm_right {a b : Int} : b ∣ lcm a b :=
  Int.dvd_trans dvd_natAbs_self (Int.ofNat_dvd.mpr (Nat.dvd_lcm_right a.natAbs b.natAbs))

@[simp] theorem lcm_self {a : Int} : lcm a a = a.natAbs := Nat.lcm_self _

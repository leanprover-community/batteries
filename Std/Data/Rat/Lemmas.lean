import Std.Data.Int.Lemmas
import Std.Data.Rat.Basic

/-! # Additional lemmas about the Rational Numbers -/

namespace Rat

@[simp] theorem maybeNormalize_eq {num den g} (den_nz reduced) :
    maybeNormalize num den g den_nz reduced =
    { num := num.div g, den := den / g, den_nz, reduced } := by
  unfold maybeNormalize; split
  · subst g; simp
  · rfl

@[simp] theorem normalize_zero (nz) : normalize 0 d nz = 0 := by
  simp [normalize, Int.zero_div, Int.natAbs_zero, Nat.div_self (Nat.pos_of_ne_zero nz)]; rfl

@[simp] theorem mk_zero : mkRat 0 n = 0 := by unfold mkRat; split <;> simp

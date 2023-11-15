/-
Copyright (c) 2023 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joe Hendrix
-/

/-
This module defines properties of the bitwise operations on Natural numbers.

It is primarily intended to support the bitvector library.
-/
import Std.Data.Nat.Lemmas

namespace Nat

@[local simp]
private theorem eq_0_of_lt_one (x:Nat) : x < 1 ↔ x = 0 :=
  Iff.intro
    (fun p =>
      match x with
      | 0 => Eq.refl 0
      | _+1 => False.elim (not_lt_zero _ (Nat.lt_of_succ_lt_succ p)))
    (fun p => by simp [p, Nat.zero_lt_succ])

private theorem eq_0_of_lt (x:Nat) : x < 2^ 0 ↔ x = 0 := eq_0_of_lt_one x

@[local simp]
private theorem zero_lt_pow (n:Nat) : 0 < 2^n := by
  induction n
  case zero => simp [eq_0_of_lt]
  case succ n hyp =>
    simp [pow_succ]
    exact (Nat.mul_lt_mul_of_pos_right hyp (by trivial : 2 > 0) : 0 < 2 ^ n * 2)

/-- This provides a bound on bitwise operations. -/
theorem bitwise_lt_2_pow (left : x < 2^n) (right : y < 2^n) : (Nat.bitwise f x y) < 2^n := by
  induction n generalizing x y with
  | zero =>
    simp only [eq_0_of_lt] at left right
    unfold bitwise
    simp [left, right]
  | succ n hyp =>
    unfold bitwise
    if x_zero : x = 0 then
      simp only [x_zero, if_true]
      by_cases p : f false true = true <;> simp [p, right]
    else if y_zero : y = 0 then
      simp only [x_zero, y_zero, if_false, if_true]
      by_cases p : f true false = true <;> simp [p, left]
    else
      simp only [x_zero, y_zero, if_false]
      have lt : 0 < 2 := by trivial
      have xlb : x / 2 < 2^n := by simp [div_lt_iff_lt_mul lt]; exact left
      have ylb : y / 2 < 2^n := by simp [div_lt_iff_lt_mul lt]; exact right
      have hyp1 := hyp xlb ylb
      by_cases p : f (decide (x % 2 = 1)) (decide (y % 2 = 1)) = true <;>
        simp [p, pow_succ, mul_succ, Nat.add_assoc]
      case pos =>
        apply lt_of_succ_le
        simp only [← Nat.succ_add]
        apply Nat.add_le_add <;> exact hyp1
      case neg =>
        apply Nat.add_lt_add <;> exact hyp1

theorem lor_lt_2_pow {x y n : Nat} (left : x < 2^n) (right : y < 2^n) : (x ||| y) < 2^n :=
  bitwise_lt_2_pow left right

theorem land_lt_2_pow {x y n : Nat} (left : x < 2^n) (right : y < 2^n) : (x &&& y) < 2^n :=
  bitwise_lt_2_pow left right

theorem xor_lt_2_pow {x y n : Nat} (left : x < 2^n) (right : y < 2^n) : (x ^^^ y) < 2^n :=
  bitwise_lt_2_pow left right

theorem shiftLeft_lt_2_pow {x m n : Nat} (bound : x < 2^(n-m)) : (x <<< m) < 2^n := by
  induction m generalizing x n with
  | zero => exact bound
  | succ m hyp =>
    simp [shiftLeft_succ_inside]
    apply hyp
    revert bound
    rw [Nat.sub_succ]
    match n - m with
    | 0 =>
      intro bound
      simp [eq_0_of_lt_one] at bound
      simp [bound]
    | d + 1 =>
      intro bound
      simp [Nat.pow_succ, Nat.mul_comm _ 2]
      exact Nat.mul_lt_mul_of_pos_left bound (by trivial : 0 < 2)

end Nat

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

/-! ### Utility -/

/--
An induction principal that works on divison by two.
-/
theorem div2InductionOn
    {motive : Nat → Sort u}
    (n : Nat)
    (base : motive 0)
    (induct : ∀(n:Nat), 0 < n → motive (n/2) → motive n)
    : motive n := by
  induction n using Nat.strongInductionOn with
  | ind x ind =>
    if x_eq : x = 0 then
      simp [x_eq]; exact base
    else
      have x_pos : x > 0 := Nat.zero_lt_of_ne_zero x_eq
      have p : x/2 < x := Nat.div_lt_self x_pos (Nat.le_refl _)
      apply induct _ x_pos (ind _ p)


/-! ### testBit -/

theorem zero_testBit (i:Nat) : testBit 0 i = false := by
  unfold testBit
  simp [zero_shiftRight]

theorem testBit_succ (x:Nat) : testBit x (succ i) = testBit (x >>> 1) i := by
  unfold testBit
  simp [shiftRight_succ_inside]

theorem land_zero (x:Nat) : x &&& 0 = 0 := by
  simp [HAnd.hAnd, AndOp.and, land]
  unfold bitwise
  simp

theorem testBit_zero_is_mod2 (x:Nat) : testBit x 0 = decide (x % 2 = 1) := by
  rw [←div_add_mod x 2]
  simp [testBit]
  simp [HAnd.hAnd, AndOp.and, land]
  unfold bitwise
  have one_div_2 : 1 / 2 = 0 := by trivial
  have elim_and := fun x => land_zero x
  simp [HAnd.hAnd, AndOp.and, land] at elim_and
  simp [one_div_2, elim_and]
  simp [Nat.add_comm (2 * _) _]
  intro x_mod
  simp [x_mod, Nat.succ_add]

theorem ne_zero_implies_bit_true {x : Nat} (p : x ≠ 0) : ∃ i, testBit x i := by
  induction x using div2InductionOn with
  | base =>
    trivial
  | induct x _ ind =>
    match mod_two_eq_zero_or_one x with
    | Or.inl mod2_eq =>
      rw [←div_add_mod x 2] at p
      simp [mod2_eq, mul_eq_zero] at p
      have ⟨d, dif⟩   := ind (p : x / 2 ≠ 0)
      apply Exists.intro (d+1)
      simp [testBit_succ]
      exact dif
    | Or.inr mod2_eq =>
      apply Exists.intro 0
      simp [testBit_zero_is_mod2, mod2_eq]

theorem ne_implies_bit_diff {x y : Nat} (p : x ≠ y) : ∃ i, testBit x i ≠ testBit y i := by
  induction y using Nat.div2InductionOn generalizing x with
  | base =>
    simp only [Nat.zero_testBit, Bool.eq_false_iff]
    have ⟨i,ip⟩  := ne_zero_implies_bit_true p
    apply Exists.intro i
    simp [ip]
  | induct y _y_pos ind_y =>
    if lsb_diff : x % 2 = y % 2 then
      rw [←Nat.div_add_mod x 2, ←Nat.div_add_mod y 2] at p
      simp [lsb_diff,
            Nat.add_right_cancel_iff,
            Nat.mul_left_cancel_iff]
        at p
      have ⟨i, ieq⟩  := ind_y p
      apply Exists.intro (i+1)
      simp [testBit_succ]
      exact ieq
    else
      apply Exists.intro 0
      simp [testBit_zero_is_mod2]
      revert lsb_diff
      cases mod_two_eq_zero_or_one x with | _ p =>
        cases mod_two_eq_zero_or_one y with | _ q =>
          simp [p,q]

/--
`eq_of_testBit_eq` allows proving two natural numbers are equal
if their bits are all equal.
-/
theorem eq_of_testBit_eq {x y : Nat} (pred : ∀i, testBit x i = testBit y i) : x = y := by
  if h : x = y then
    exact h
  else
    let ⟨i,eq⟩ := ne_implies_bit_diff h
    have p := pred i
    contradiction

/-! ### bitwise and related -/

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

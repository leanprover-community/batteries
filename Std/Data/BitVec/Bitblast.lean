/-
Copyright (c) 2023 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Harun Khan, Abdalrhman M Mohamed
-/
import Std.Data.BitVec.Basic
import Std.Data.Nat.Lemmas
import Std.Data.Bool

namespace Std
open Nat Bool

/-! ### Preliminaries -/

theorem bodd_eq_bodd_iff {m n} : bodd n = bodd m ↔ n % 2 = m % 2 := by
  cases hn : bodd n <;> cases hm : bodd m
  <;> simp [mod_two_of_bodd, hn, hm]

theorem testBit_two_pow_mul_add {n b w i} (h: i < w) :
    Nat.testBit (2 ^ w * b + n) i = Nat.testBit n i := by
  simp only [testBit, shiftRight_eq_div_pow, bodd_eq_bodd_iff]
  rw [← Nat.add_sub_of_le (succ_le_of_lt h), Nat.succ_eq_add_one, Nat.add_assoc]
  rw [Nat.pow_add, Nat.add_comm, Nat.mul_assoc, add_mul_div_left _ _ (two_pow_pos _), add_mod]
  rw [Nat.pow_add, Nat.pow_one, Nat.mul_assoc]
  simp

theorem testBit_two_pow_mul_toNat_add {n w b} (h: n < 2 ^ w) :
    testBit (2 ^ w * (bit b 0) + n) w = b := by
  simp only [testBit, shiftRight_eq_div_pow]
  rw [Nat.add_comm, add_mul_div_left _ _ (two_pow_pos _), Nat.div_eq_of_lt h, Nat.zero_add]
  cases b <;> simp

@[simp] theorem toNat_eq_bif {b: Bool}: cond b 1 0 = toNat b := by simp [cond, toNat]

theorem shiftRight_eq_testBit (x i : Nat) : (x >>> i) % 2 = toNat (testBit x i) := by
  simp [Nat.testBit, Nat.mod_two_of_bodd, toNat_eq_bif]

theorem div_add_mod_two_pow (m n : Nat) : n = 2 ^ m * n >>> m + n % (2 ^ m):= by
  simp [shiftRight_eq_div_pow, Nat.div_add_mod]

theorem mod_two_pow_succ (x i : Nat) :
  x % 2 ^ (i + 1) = 2 ^ i * toNat (Nat.testBit x i) + x % (2 ^ i):= by
  have h1 := div_add_mod_two_pow i x
  rw [←div_add_mod (x >>> i) 2, Nat.mul_add, ←Nat.mul_assoc, ←pow_succ, shiftRight_eq_testBit] at h1
  have h2 := Eq.trans (div_add_mod_two_pow (i + 1) x).symm h1
  rw [shiftRight_succ, succ_eq_add_one, Nat.add_assoc] at h2
  exact Nat.add_left_cancel h2

/-- Generic method to create a natural number by appending bits tail-recursively.
It takes a boolean function `f` on each bit the number of bits `i`.  It is
almost always specialized  `i = w`; the length of the binary representation.
This is an alternative to using `List` and is used to define bitadd, bitneg, bitmul etc.-/
def ofBits (f : Nat → Bool) (z : Nat) : Nat → Nat
  | 0 => z
  | i + 1 => ofBits f (z.bit (f i)) i

theorem ofBits_succ {f : Nat → Bool} {i z : Nat} : ofBits f z i = 2 ^ i * z + ofBits f 0 i:= by
  revert z
  induction i with
  | zero => simp [ofBits, bit_val]
  | succ i ih =>  intro z; simp only [ofBits, @ih (bit (f i) 0), @ih (bit (f i) z)]
                  rw [bit_val, Nat.mul_add, ← Nat.mul_assoc, ← pow_succ]
                  simp [bit_val, Nat.add_assoc]

theorem ofBits_lt {f: Nat → Bool} : ofBits f 0 i < 2^i := by
  induction i with
  | zero => simp [ofBits, bit_val, lt_succ]
  | succ i ih =>  simp only [ofBits]
                  rw [ofBits_succ, two_pow_succ]
                  cases (f i)
                  · exact add_lt_add (by simp [bit_val, two_pow_pos i]) ih
                  · simp only [bit_val, Nat.mul_zero, cond_true, Nat.zero_add, Nat.mul_one]
                    exact Nat.add_lt_add_left ih _

theorem ofBits_testBit {f : Nat → Bool} (h1: i < j) : (ofBits f 0 j).testBit i = f i := by
  cases j with
  | zero => simp [not_lt_zero] at h1
  | succ j =>
    revert i
    induction j with
    | zero => simp [lt_succ, ofBits, bit_val]
              cases (f 0) <;> trivial
    | succ j ih =>
      intro i hi
      rw [lt_succ] at hi
      cases Nat.lt_or_eq_of_le hi with
      | inl h1 => rw [← ih h1, ofBits, ofBits_succ, testBit_two_pow_mul_add h1]
      | inr h1 => rw [h1, ofBits, ofBits_succ, testBit_two_pow_mul_toNat_add (ofBits_lt)]

/-! ### Addition -/

/-- Carry function for bitwise addition. -/
def bitwise_carry (x y : Nat) : Nat → Bool
  | 0     => false
  | i + 1 => (x.testBit i && y.testBit i) || ((x.testBit i ^^ y.testBit i) && bitwise_carry x y i)

/-- Bitwise addition implemented via a ripple carry adder. -/
@[simp] def bitwise_add (x y i: Nat) :=
  ofBits (λ j => (x.testBit j ^^ y.testBit j) ^^ bitwise_carry x y j) 0 i

theorem bitwise_add_eq_add_base (x y i: Nat) :
  x % (2 ^ i) + y % (2 ^ i) = bitwise_add x y i + 2 ^ i * toNat (bitwise_carry x y i) := by
  induction i with
  | zero => simp [mod_one, ofBits, bitwise_carry]
  | succ i hi => rw [mod_two_pow_succ x, mod_two_pow_succ y]
                 rw [Nat.add_assoc, Nat.add_comm _ (y % 2 ^ i), ← Nat.add_assoc (x % 2 ^ i)]
                 rw [hi, bitwise_carry, two_pow_succ i]
                 cases hx : Nat.testBit x i <;> cases hy : Nat.testBit y i
                 <;> cases hc : bitwise_carry x y i
                 <;> simp [bit_val, toNat, @ofBits_succ _ i 1, two_pow_succ, hx, hy, hc,
                           ofBits, Nat.add_comm, Nat.add_assoc]

theorem bitwise_add_eq_add (x y : Nat) : bitwise_add x y i = (x + y) % 2 ^ i := by
  rw [Nat.add_mod, bitwise_add_eq_add_base]
  cases i
  · simp [mod_one, ofBits]
  · simp [bitwise_add, Nat.mod_eq_of_lt ofBits_lt]

theorem BV_add {x y : BitVec w}: bitwise_add (x.toNat) y.toNat w = (x + y).toNat := by
  rw [bitwise_add_eq_add]
  rfl

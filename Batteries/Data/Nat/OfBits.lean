/-
Copyright (c) 2025 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: François G. Dorais
-/

namespace Nat

/-- Construct a natural number from bit values (little endian). -/
@[inline] def ofBits (f : Fin n → Bool) : Nat :=
  Fin.foldr n (fun i v => 2 * v + (f i).toNat) 0

@[simp] theorem ofBits_zero (f : Fin 0 → Bool) : ofBits f = 0 := rfl

@[simp] theorem ofBits_one (f : Fin 1 → Bool) : ofBits f = (f 0).toNat := Nat.zero_add ..

theorem ofBits_succ (f : Fin (n+1) → Bool) :
    ofBits f = 2 * ofBits (f ∘ Fin.succ) + (f 0).toNat := by
  simp [ofBits, Fin.foldr_succ]

theorem ofBits_lt_two_pow (f : Fin n → Bool) : ofBits f < 2 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc ofBits f
        = 2 * ofBits (f ∘ Fin.succ) + (f 0).toNat := ofBits_succ ..
      _ ≤ 2 * ofBits (f ∘ Fin.succ) + 1 := Nat.add_le_add_left (Bool.toNat_le _) ..
      _ < 2 * (ofBits (f ∘ Fin.succ) + 1) := Nat.lt_add_one ..
      _ ≤ 2 * 2 ^ n := Nat.mul_le_mul_left 2 (Nat.succ_le_of_lt (ih _))
      _ = 2 ^ (n + 1) := (Nat.pow_add_one' ..).symm

@[simp] theorem testBit_ofBits_lt (f : Fin n → Bool) (i) (h : i < n) :
    (ofBits f).testBit i = f ⟨i, h⟩ := by
  induction n generalizing i with
  | zero => contradiction
  | succ n ih =>
    have h0 : (f 0).toNat < 2 := Bool.toNat_lt ..
    match i with
    | 0 =>
      rw [ofBits_succ, testBit_zero, Nat.mul_add_mod, Nat.mod_eq_of_lt h0, Fin.zero_eta]
      cases f 0 <;> rfl
    | i+1 =>
      rw [ofBits_succ, testBit_add_one, Nat.mul_add_div Nat.zero_lt_two, Nat.div_eq_of_lt h0]
      exact ih (f ∘ Fin.succ) i (Nat.lt_of_succ_lt_succ h)

@[simp] theorem testBit_ofBits_ge (f : Fin n → Bool) (i) (h : n ≤ i) :
    (ofBits f).testBit i = false := by
  induction n generalizing i with
  | zero => simp
  | succ n ih =>
    have h0 : (f 0).toNat < 2 := Bool.toNat_lt ..
    match i with
    | i+1 =>
      rw [ofBits_succ, testBit_succ, Nat.mul_add_div Nat.zero_lt_two, Nat.div_eq_of_lt h0]
      exact ih (f ∘ Fin.succ) i (Nat.le_of_succ_le_succ h)

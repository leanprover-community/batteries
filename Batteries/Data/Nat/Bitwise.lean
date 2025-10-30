/-
Copyright (c) 2025 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: François G. Dorais
-/

/-! # Bitwise Lemmas

This module defines properties of the bitwise operations on natural numbers.

This file is complements `Init.Data.Nat.Bitwise.Lemmas` with properties that
are not necessary for the bitvector library.
-/

namespace Nat

/-! ### and -/

@[simp] theorem and_self_left (a b : Nat) : a &&& (a &&& b) = a &&& b := by
  apply Nat.eq_of_testBit_eq; simp

@[simp] theorem and_self_right (a b : Nat) : ((a &&& b) &&& b) = (a &&& b) := by
  apply Nat.eq_of_testBit_eq; simp

theorem and_left_comm (x y z : Nat) : x &&& (y &&& z) = y &&& (x &&& z) := by
  apply Nat.eq_of_testBit_eq; simp [Bool.and_left_comm]

theorem and_right_comm (x y z : Nat) : (x &&& y) &&& z = (x &&& z) &&& y := by
  apply Nat.eq_of_testBit_eq; simp [Bool.and_right_comm]

/-! ### or -/

@[simp] theorem or_self_left (a b : Nat) : a ||| (a ||| b) = a ||| b := by
  apply Nat.eq_of_testBit_eq; simp

@[simp] theorem or_self_right (a b : Nat) : (a ||| b) ||| b = a ||| b := by
  apply Nat.eq_of_testBit_eq; simp

theorem or_left_comm (x y z : Nat) : x ||| (y ||| z) = y ||| (x ||| z) := by
  apply Nat.eq_of_testBit_eq; simp [Bool.or_left_comm]

theorem or_right_comm (x y z : Nat) : (x ||| y) ||| z = (x ||| z) ||| y := by
  apply Nat.eq_of_testBit_eq; simp [Bool.or_right_comm]

/-! ### xor -/

theorem xor_left_comm (x y z : Nat) : x ^^^ (y ^^^ z) = y ^^^ (x ^^^ z) := by
  apply Nat.eq_of_testBit_eq; simp only [testBit_xor, Bool.xor_left_comm, implies_true]

theorem xor_right_comm (x y z : Nat) : (x ^^^ y) ^^^ z = (x ^^^ z) ^^^ y := by
  apply Nat.eq_of_testBit_eq; simp only [testBit_xor, Bool.xor_right_comm, implies_true]

@[simp] theorem xor_xor_cancel_left (x y : Nat) : x ^^^ (x ^^^ y) = y := by
  apply Nat.eq_of_testBit_eq; simp

@[simp] theorem xor_xor_cancel_right (x y : Nat) : (x ^^^ y) ^^^ y = x := by
  apply Nat.eq_of_testBit_eq; simp

theorem eq_of_xor_eq_zero {x y : Nat} : x ^^^ y = 0 → x = y := by
  intro h; rw [← xor_xor_cancel_left x y, h, xor_zero]

@[simp] theorem xor_eq_zero_iff {x y : Nat} : x ^^^ y = 0 ↔ x = y :=
  ⟨eq_of_xor_eq_zero, fun | rfl => Nat.xor_self _⟩

theorem xor_ne_zero_iff {x y : Nat} : x ^^^ y ≠ 0 ↔ x ≠ y := by simp

/-! ### injectivity lemmas -/

theorem xor_right_injective {x : Nat} : Function.Injective (x ^^^ ·) := by
  intro y z h; rw [← xor_xor_cancel_left x y, ← xor_xor_cancel_left x z]; simp only [h]

theorem xor_left_injective {x : Nat} : Function.Injective (· ^^^ x) := by
  intro y z h; rw [← xor_xor_cancel_right y x, ← xor_xor_cancel_right z x]; simp only [h]

@[simp] theorem xor_right_inj {x y z : Nat} : x ^^^ y = x ^^^ z ↔ y = z :=
  ⟨(xor_right_injective ·), fun | rfl => rfl⟩

@[simp] theorem xor_left_inj {x y z : Nat} : x ^^^ z = y ^^^ z ↔ x = y :=
  ⟨(xor_left_injective ·), fun | rfl => rfl⟩

theorem and_or_right_injective {m x y : Nat} : x &&& m = y &&& m → x ||| m = y ||| m → x = y := by
  intro ha ho
  apply Nat.eq_of_testBit_eq
  intro i
  rw [← Bool.and_or_inj_right_iff (m := m.testBit i)]
  simp [← testBit_and, ← testBit_or, ha, ho]

theorem and_or_right_inj {m x y : Nat} : x &&& m = y &&& m ∧ x ||| m = y ||| m ↔ x = y :=
  ⟨fun ⟨ha, ho⟩ => and_or_right_injective ha ho, fun | rfl => ⟨rfl, rfl⟩⟩

theorem and_or_left_injective {m x y : Nat} : m &&& x = m &&& y → m ||| x = m ||| y → x = y := by
  intro ha ho
  apply Nat.eq_of_testBit_eq
  intro i
  rw [← Bool.and_or_inj_left_iff (m := m.testBit i)]
  simp [← testBit_and, ← testBit_or, ha, ho]

theorem and_or_left_inj {m x y : Nat} : m &&& x = m &&& y ∧ m ||| x = m ||| y ↔ x = y :=
  ⟨fun ⟨ha, ho⟩ => and_or_left_injective ha ho, fun | rfl => ⟨rfl, rfl⟩⟩

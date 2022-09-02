/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad
-/

namespace Nat

theorem lt_succ_of_lt (h : a < b) : a < succ b := le_succ_of_le h

@[simp] theorem shiftLeft_eq (a b : Nat) : a <<< b = a * 2 ^ b :=
  match b with
  | 0 => (Nat.mul_one _).symm
  | b+1 => (shiftLeft_eq _ b).trans <| by
    simp [pow_succ, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]

theorem one_shiftLeft (n : Nat) : 1 <<< n = 2 ^ n := by rw [shiftLeft_eq, Nat.one_mul]

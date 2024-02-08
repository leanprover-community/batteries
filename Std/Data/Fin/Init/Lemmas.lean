/-
Copyright (c) 2023 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/

namespace Fin

@[simp] theorem zero_eta : (⟨0, Nat.zero_lt_succ _⟩ : Fin (n + 1)) = 0 := rfl

theorem val_inj {a b : Fin n} : a.1 = b.1 ↔ a = b := ⟨Fin.eq_of_val_eq, Fin.val_eq_of_eq⟩

theorem val_congr {n : Nat} {a b : Fin n} (h : a = b) : (a : Nat) = (b : Nat) :=
  Fin.val_inj.mpr h

theorem val_le_of_le {n : Nat} {a b : Fin n} (h : a ≤ b) : (a : Nat) ≤ (b : Nat) := h

theorem val_le_of_ge {n : Nat} {a b : Fin n} (h : a ≥ b) : (b : Nat) ≤ (a : Nat) := h

theorem val_add_one_le_of_lt {n : Nat} {a b : Fin n} (h : a < b) : (a : Nat) + 1 ≤ (b : Nat) := h

theorem val_add_one_le_of_gt {n : Nat} {a b : Fin n} (h : a > b) : (b : Nat) + 1 ≤ (a : Nat) := h

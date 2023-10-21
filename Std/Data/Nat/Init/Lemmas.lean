/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad, Mario Carneiro
-/
import Std.Logic

namespace Nat

theorem succ_sub {m n : Nat} (h : n ≤ m) : succ m - n = succ (m - n) := by
  let ⟨k, hk⟩ := Nat.le.dest h
  rw [← hk, Nat.add_sub_cancel_left, ← add_succ, Nat.add_sub_cancel_left]

protected theorem sub_le_sub_right {n m : Nat} (h : n ≤ m) : ∀ k, n - k ≤ m - k
  | 0   => h
  | z+1 => pred_le_pred (Nat.sub_le_sub_right h z)

protected theorem sub_lt_left_of_lt_add {n k m : Nat} (H : n ≤ k) (h : k < n + m) : k - n < m := by
  have := Nat.sub_le_sub_right (succ_le_of_lt h) n
  rwa [Nat.add_sub_cancel_left, Nat.succ_sub H] at this

protected theorem sub_lt_right_of_lt_add {n k m : Nat} (H : n ≤ k) (h : k < m + n) : k - n < m :=
  Nat.sub_lt_left_of_lt_add H (Nat.add_comm .. ▸ h)

protected theorem pos_of_ne_zero {n : Nat} : n ≠ 0 → 0 < n := (eq_zero_or_pos n).resolve_left

protected theorem min_eq_min (a : Nat) : Nat.min a b = min a b := rfl

protected theorem max_eq_max (a : Nat) : Nat.max a b = max a b := rfl

protected theorem min_comm (a b : Nat) : min a b = min b a := by
  simp [Nat.min_def]; split <;> split <;> try simp [*]
  · next h₁ h₂ => exact Nat.le_antisymm h₁ h₂
  · next h₁ h₂ => cases not_or_intro h₁ h₂ <| Nat.le_total ..

protected theorem min_le_right (a b : Nat) : min a b ≤ b := by rw [Nat.min_def]; split <;> simp [*]

protected theorem min_le_left (a b : Nat) : min a b ≤ a := Nat.min_comm .. ▸ Nat.min_le_right ..

protected theorem max_comm (a b : Nat) : max a b = max b a := by
  simp only [Nat.max_def]
  by_cases h₁ : a ≤ b <;> by_cases h₂ : b ≤ a <;> simp [h₁, h₂]
  · exact Nat.le_antisymm h₂ h₁
  · cases not_or_intro h₁ h₂ <| Nat.le_total ..

protected theorem le_max_left (a b : Nat) : a ≤ max a b := by rw [Nat.max_def]; split <;> simp [*]

protected theorem le_max_right (a b : Nat) : b ≤ max a b := Nat.max_comm .. ▸ Nat.le_max_left ..

protected theorem pow_two_pos (w : Nat) : 0 < 2^w := Nat.pos_pow_of_pos _ (by decide)

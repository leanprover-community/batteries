/-
Copyright (c) 2025 Marcus Rossel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rossel
-/

namespace Nat

@[simp]
theorem isDigit_digitChar : n.digitChar.isDigit = decide (n < 10) :=
  match n with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 => by simp [digitChar]
  | _ + 10 => by
    simp only [digitChar, ↓reduceIte, Nat.reduceEqDiff]
    (repeat' split) <;> simp

private theorem isDigit_of_mem_toDigitsCore
    (hc : c ∈ cs → c.isDigit) (hb₁ : 0 < b) (hb₂ : b ≤ 10) (h : c ∈ toDigitsCore b fuel n cs) :
    c.isDigit := by
  induction fuel generalizing n cs <;> rw [toDigitsCore] at h
  next => exact hc h
  next fuel ih =>
    split at h
    case' isFalse => apply ih (fun h => ?_) h
    all_goals
      cases h
      next => simp [Nat.lt_of_lt_of_le (mod_lt _ hb₁) hb₂]
      next hm => exact hc hm

theorem isDigit_of_mem_toDigits (hb₁ : 0 < b) (hb₂ : b ≤ 10) (hc : c ∈ toDigits b n) : c.isDigit :=
  isDigit_of_mem_toDigitsCore (fun _ => by contradiction) hb₁ hb₂ hc

theorem toDigits_10_of_lt (h : n < b) : toDigits b n = [n.digitChar] := by
  simp_all [toDigits, toDigitsCore, mod_eq_of_lt]

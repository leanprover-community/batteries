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

private theorem isDigit_of_mem_toDigitsCore_10
    (hf : n < fuel) (hc : c ∈ cs → c.isDigit) (h : c ∈ toDigitsCore 10 fuel n cs) :
    c.isDigit := by
  induction fuel generalizing n cs <;> rw [toDigitsCore] at h
  next => contradiction
  next fuel ih =>
    split at h
    case' isFalse => apply ih (by omega) (fun h => ?_) h
    all_goals
      cases h
      next => simp [mod_lt]
      next hm => exact hc hm

theorem isDigit_of_mem_toDigits_10 (h : c ∈ toDigits 10 n) : c.isDigit :=
  isDigit_of_mem_toDigitsCore_10 (Nat.lt_succ_self _) (fun _ => by contradiction) h

theorem toDigits_10_of_lt_10 (h : n < 10) : toDigits 10 n = [n.digitChar] :=
  match n with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 => by decide
  | _ + 10                                => by contradiction

@[simp]
theorem toDigits_10_natAbs_ofNat (n : Nat) : toDigits 10 (n : Int).natAbs = toDigits 10 n := by
  simp

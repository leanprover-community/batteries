/-
Copyright (c) 2025 Marcus Rossel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rossel
-/

namespace Nat

theorem isDigit_digitChar_of_lt (h : n < 10) : n.digitChar.isDigit := by
  match n with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 => simp [*, digitChar]
  | _ + 10                                => contradiction

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
      next => have := isDigit_digitChar_of_lt (mod_lt n <| by decide); simp_all
      next hm => exact hc hm

theorem isDigit_of_mem_toDigits_10 (h : c ∈ toDigits 10 n) : c.isDigit :=
  isDigit_of_mem_toDigitsCore_10 (Nat.lt_succ_self _) (fun _ => by contradiction) h

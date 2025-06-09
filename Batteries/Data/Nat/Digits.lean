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
  induction fuel generalizing n cs with rw [toDigitsCore] at h
  | zero => exact hc h
  | succ _ ih =>
    split at h
    case' isFalse => apply ih (fun h => ?_) h
    all_goals
      cases h with
      | head      => simp [Nat.lt_of_lt_of_le (mod_lt _ hb₁) hb₂]
      | tail _ hm => exact hc hm

theorem isDigit_of_mem_toDigits (hb₁ : 0 < b) (hb₂ : b ≤ 10) (hc : c ∈ toDigits b n) : c.isDigit :=
  isDigit_of_mem_toDigitsCore (fun _ => by contradiction) hb₁ hb₂ hc

private theorem toDigitsCore_of_lt_base (hb : n < b) (hf : n < fuel) :
    toDigitsCore b fuel n cs = n.digitChar :: cs := by
  unfold toDigitsCore
  split <;> simp_all [mod_eq_of_lt]

theorem toDigits_of_lt_base (h : n < b) : toDigits b n = [n.digitChar] :=
  toDigitsCore_of_lt_base h (lt_succ_self _)

theorem toDigits_zero : (b : Nat) → toDigits b 0 = ['0']
  | 0     => rfl
  | _ + 1 => toDigits_of_lt_base (zero_lt_succ _)

private theorem toDigitsCore_append :
    toDigitsCore b fuel n cs₁ ++ cs₂ = toDigitsCore b fuel n (cs₁ ++ cs₂) := by
  induction fuel generalizing n cs₁ with simp only [toDigitsCore]
  | succ => split <;> simp_all

private theorem toDigitsCore_eq_of_lt_fuel (hb : 1 < b) (h₁ : n < fuel₁) (h₂ : n < fuel₂) :
    toDigitsCore b fuel₁ n cs = toDigitsCore b fuel₂ n cs := by
  cases fuel₁ <;> cases fuel₂ <;> try contradiction
  simp only [toDigitsCore, Nat.div_eq_zero_iff]
  split
  · simp
  · have := Nat.div_lt_self (by omega : 0 < n) hb
    exact toDigitsCore_eq_of_lt_fuel hb (by omega) (by omega)

private theorem toDigitsCore_toDigitsCore
    (hb₁ : 1 < b) (hb₂ : b ≤ 10) (hn : 0 < n) (hd : d < b)
    (hf : (b * n + d) < fuel) (hnf : n < nFuel) (hdf : d < dFuel) :
    toDigitsCore b nFuel n (toDigitsCore b dFuel d cs) = toDigitsCore b fuel (b * n + d) cs := by
  cases fuel with
  | zero => contradiction
  | succ fuel =>
    rw [toDigitsCore]
    split
    case isTrue h =>
      have : b ≤ b * n + d := Nat.le_trans (Nat.le_mul_of_pos_right _ hn) (le_add_right _ _)
      cases Nat.div_eq_zero_iff.mp h <;> omega
    case isFalse =>
      have h : (b * n + d) / b = n := by
        rw [mul_add_div (by omega), Nat.div_eq_zero_iff.mpr (.inr hd), Nat.add_zero]
      have := (Nat.lt_mul_iff_one_lt_left hn).mpr hb₁
      simp only [toDigitsCore_of_lt_base hd hdf, mul_add_mod_self_left, mod_eq_of_lt hd, h]
      apply toDigitsCore_eq_of_lt_fuel hb₁ hnf (by omega)

theorem toDigits_append_toDigits (hb₁ : 1 < b) (hb₂ : b ≤ 10) (hn : 0 < n) (hd : d < b) :
    (toDigits b n) ++ (toDigits b d) = toDigits b (b * n + d) := by
  rw [toDigits, toDigitsCore_append]
  exact toDigitsCore_toDigitsCore hb₁ hb₂ hn hd (lt_succ_self _) (lt_succ_self _) (lt_succ_self _)

/-
Copyright (c) 2024 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: François G. Dorais
-/
import Batteries.Tactic.Basic
import Batteries.Data.Nat.Basic

namespace Nat

/-- Average of two natural numbers rounded toward zero. -/
abbrev avg (a b : Nat) := (a + b) / 2

theorem avg_comm (a b : Nat) : avg a b = avg b a := by
  rw [avg, Nat.add_comm]

theorem avg_le_left (h : b ≤ a) : avg a b ≤ a := by
  apply Nat.div_le_of_le_mul; simp +arith [*]

theorem avg_le_right (h : a ≤ b) : avg a b ≤ b := by
  apply Nat.div_le_of_le_mul; simp +arith [*]

theorem avg_lt_left (h : b < a) : avg a b < a := by
  apply Nat.div_lt_of_lt_mul; omega

theorem avg_lt_right (h : a < b) : avg a b < b := by
  apply Nat.div_lt_of_lt_mul; omega

theorem le_avg_left (h : a ≤ b) : a ≤ avg a b := by
  apply (Nat.le_div_iff_mul_le Nat.zero_lt_two).mpr; simp +arith [*]

theorem le_avg_right (h : b ≤ a) : b ≤ avg a b := by
  apply (Nat.le_div_iff_mul_le Nat.zero_lt_two).mpr; simp +arith [*]

theorem le_add_one_of_avg_eq_left (h : avg a b = a) : b ≤ a + 1 := by
  cases Nat.lt_or_ge b (a+2) with
  | inl hlt => exact Nat.le_of_lt_add_one hlt
  | inr hge =>
    absurd Nat.lt_irrefl a
    conv => rhs; rw [← h]
    rw [← Nat.add_one_le_iff, Nat.le_div_iff_mul_le Nat.zero_lt_two]
    omega

theorem le_add_one_of_avg_eq_right (h : avg a b = b) : a ≤ b + 1 := by
  cases Nat.lt_or_ge a (b+2) with
  | inl hlt => exact Nat.le_of_lt_add_one hlt
  | inr hge =>
    absurd Nat.lt_irrefl b
    conv => rhs; rw [← h]
    rw [← Nat.add_one_le_iff, Nat.le_div_iff_mul_le Nat.zero_lt_two]
    omega

/--
Given natural numbers `a < b` such that `p a = true` and `p b = false`, `bisect` finds a natural
number `a ≤ c < b` such that `p c = true` and `p (c+1) = false`.
-/
def bisect {p : Nat → Bool} (h : start < stop) (hstart : p start = true) (hstop : p stop = false) :=
  let mid := avg start stop
  have hmidstop : mid < stop := by apply Nat.div_lt_of_lt_mul; omega
  if hstartmid : start < mid then
    match hmid : p mid with
    | false => bisect hstartmid hstart hmid
    | true => bisect hmidstop hmid hstop
  else
    mid
termination_by stop - start

theorem bisect_lt_stop {p : Nat → Bool} (h : start < stop) (hstart : p start = true)
    (hstop : p stop = false) : bisect h hstart hstop < stop := by
  unfold bisect
  simp only; split
  · split
    · next h' _ =>
      have : avg start stop - start < stop - start := by
        apply Nat.sub_lt_sub_right
        · exact Nat.le_of_lt h'
        · exact Nat.avg_lt_right h
      apply Nat.lt_trans
      · exact bisect_lt_stop ..
      · exact avg_lt_right h
    · exact bisect_lt_stop ..
  · exact avg_lt_right h

theorem start_le_bisect {p : Nat → Bool} (h : start < stop) (hstart : p start = true)
    (hstop : p stop = false) : start ≤ bisect h hstart hstop := by
  unfold bisect
  simp only; split
  · split
    · next h' _ =>
      have : avg start stop - start < stop - start := by
        apply Nat.sub_lt_sub_right
        · exact Nat.le_of_lt h'
        · exact avg_lt_right h
      exact start_le_bisect ..
    · next h' _ =>
      apply Nat.le_trans
      · exact Nat.le_of_lt h'
      · exact start_le_bisect ..
  · exact le_avg_left (Nat.le_of_lt h)

theorem bisect_true {p : Nat → Bool} (h : start < stop) (hstart : p start = true)
    (hstop : p stop = false) : p (bisect h hstart hstop) = true := by
  unfold bisect
  simp only; split
  · split
    · have : avg start stop - start < stop - start := by
        apply Nat.sub_lt_sub_right
        · exact Nat.le_avg_left (Nat.le_of_lt h)
        · exact Nat.avg_lt_right h
      exact bisect_true ..
    · exact bisect_true ..
  · next h' =>
    rw [← hstart]; congr
    apply Nat.le_antisymm
    · exact Nat.le_of_not_gt h'
    · exact Nat.le_avg_left (Nat.le_of_lt h)

theorem bisect_add_one_false {p : Nat → Bool} (h : start < stop) (hstart : p start = true)
    (hstop : p stop = false) : p (bisect h hstart hstop + 1) = false := by
  unfold bisect
  simp only; split
  · split
    · have : avg start stop - start < stop - start := by
        apply Nat.sub_lt_sub_right
        · exact Nat.le_avg_left (Nat.le_of_lt h)
        · exact Nat.avg_lt_right h
      exact bisect_add_one_false ..
    · exact bisect_add_one_false ..
  · next h' =>
    have heq : avg start stop = start := by
      apply Nat.le_antisymm
      · exact Nat.le_of_not_gt h'
      · exact Nat.le_avg_left (Nat.le_of_lt h)
    rw [← hstop, heq]; congr
    apply Nat.le_antisymm
    · exact Nat.succ_le_of_lt h
    · exact Nat.le_add_one_of_avg_eq_left heq

/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Deniz Aydin, Floris van Doorn, Mario Carneiro
-/
import Std.Data.Nat.Lemmas

/-!
# Results about the order properties of the integers, and the integers as an ordered ring.
-/

open Nat

namespace Int

/-! ## Order properties of the integers -/

protected alias ⟨lt_of_not_ge, not_le_of_gt⟩ := Int.not_le

protected theorem le_of_not_le {a b : Int} : ¬ a ≤ b → b ≤ a := (Int.le_total a b).resolve_left

@[simp] theorem negSucc_not_pos (n : Nat) : 0 < -[n+1] ↔ False := by
  simp only [Int.not_lt, iff_false]; constructor

theorem eq_negSucc_of_lt_zero : ∀ {a : Int}, a < 0 → ∃ n : Nat, a = -[n+1]
  | ofNat _, h => absurd h (Int.not_lt.2 (ofNat_zero_le _))
  | -[n+1],  _ => ⟨n, rfl⟩

protected theorem lt_of_add_lt_add_left {a b c : Int} (h : a + b < a + c) : b < c := by
  have : -a + (a + b) < -a + (a + c) := Int.add_lt_add_left h _
  simp [Int.neg_add_cancel_left] at this
  assumption

protected theorem lt_of_add_lt_add_right {a b c : Int} (h : a + b < c + b) : a < c :=
  Int.lt_of_add_lt_add_left (a := b) <| by rwa [Int.add_comm b a, Int.add_comm b c]

protected theorem add_lt_add_iff_left (a : Int) : a + b < a + c ↔ b < c :=
  ⟨Int.lt_of_add_lt_add_left, (Int.add_lt_add_left · _)⟩

protected theorem add_lt_add_iff_right (c : Int) : a + c < b + c ↔ a < b :=
  ⟨Int.lt_of_add_lt_add_right, (Int.add_lt_add_right · _)⟩

protected theorem add_lt_add {a b c d : Int} (h₁ : a < b) (h₂ : c < d) : a + c < b + d :=
  Int.lt_trans (Int.add_lt_add_right h₁ c) (Int.add_lt_add_left h₂ b)

protected theorem add_lt_add_of_le_of_lt {a b c d : Int} (h₁ : a ≤ b) (h₂ : c < d) :
    a + c < b + d :=
  Int.lt_of_le_of_lt (Int.add_le_add_right h₁ c) (Int.add_lt_add_left h₂ b)

protected theorem add_lt_add_of_lt_of_le {a b c d : Int} (h₁ : a < b) (h₂ : c ≤ d) :
    a + c < b + d :=
  Int.lt_of_lt_of_le (Int.add_lt_add_right h₁ c) (Int.add_le_add_left h₂ b)

protected theorem lt_add_of_pos_right (a : Int) {b : Int} (h : 0 < b) : a < a + b := by
  have : a + 0 < a + b := Int.add_lt_add_left h a
  rwa [Int.add_zero] at this

protected theorem lt_add_of_pos_left (a : Int) {b : Int} (h : 0 < b) : a < b + a := by
  have : 0 + a < b + a := Int.add_lt_add_right h a
  rwa [Int.zero_add] at this

protected theorem add_nonneg {a b : Int} (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a + b :=
  Int.zero_add 0 ▸ Int.add_le_add ha hb

protected theorem add_pos {a b : Int} (ha : 0 < a) (hb : 0 < b) : 0 < a + b :=
  Int.zero_add 0 ▸ Int.add_lt_add ha hb

protected theorem add_pos_of_pos_of_nonneg {a b : Int} (ha : 0 < a) (hb : 0 ≤ b) : 0 < a + b :=
  Int.zero_add 0 ▸ Int.add_lt_add_of_lt_of_le ha hb

protected theorem add_pos_of_nonneg_of_pos {a b : Int} (ha : 0 ≤ a) (hb : 0 < b) : 0 < a + b :=
  Int.zero_add 0 ▸ Int.add_lt_add_of_le_of_lt ha hb

protected theorem add_nonpos {a b : Int} (ha : a ≤ 0) (hb : b ≤ 0) : a + b ≤ 0 :=
  Int.zero_add 0 ▸ Int.add_le_add ha hb

protected theorem add_neg {a b : Int} (ha : a < 0) (hb : b < 0) : a + b < 0 :=
  Int.zero_add 0 ▸ Int.add_lt_add ha hb

protected theorem add_neg_of_neg_of_nonpos {a b : Int} (ha : a < 0) (hb : b ≤ 0) : a + b < 0 :=
  Int.zero_add 0 ▸ Int.add_lt_add_of_lt_of_le ha hb

protected theorem add_neg_of_nonpos_of_neg {a b : Int} (ha : a ≤ 0) (hb : b < 0) : a + b < 0 :=
  Int.zero_add 0 ▸ Int.add_lt_add_of_le_of_lt ha hb

protected theorem lt_add_of_le_of_pos {a b c : Int} (hbc : b ≤ c) (ha : 0 < a) : b < c + a :=
  Int.add_zero b ▸ Int.add_lt_add_of_le_of_lt hbc ha

theorem add_one_le_iff {a b : Int} : a + 1 ≤ b ↔ a < b := .rfl

theorem lt_add_one_iff {a b : Int} : a < b + 1 ↔ a ≤ b := Int.add_le_add_iff_right _

@[simp] theorem succ_ofNat_pos (n : Nat) : 0 < (n : Int) + 1 :=
  lt_add_one_iff.2 (ofNat_zero_le _)

theorem le_add_one {a b : Int} (h : a ≤ b) : a ≤ b + 1 :=
  Int.le_of_lt (Int.lt_add_one_iff.2 h)

protected theorem nonneg_of_neg_nonpos {a : Int} (h : -a ≤ 0) : 0 ≤ a :=
  Int.le_of_neg_le_neg <| by rwa [Int.neg_zero]

protected theorem nonpos_of_neg_nonneg {a : Int} (h : 0 ≤ -a) : a ≤ 0 :=
  Int.le_of_neg_le_neg <| by rwa [Int.neg_zero]

protected theorem lt_of_neg_lt_neg {a b : Int} (h : -b < -a) : a < b :=
  Int.neg_neg a ▸ Int.neg_neg b ▸ Int.neg_lt_neg h

protected theorem pos_of_neg_neg {a : Int} (h : -a < 0) : 0 < a :=
  Int.lt_of_neg_lt_neg <| by rwa [Int.neg_zero]

protected theorem neg_of_neg_pos {a : Int} (h : 0 < -a) : a < 0 :=
  have : -0 < -a := by rwa [Int.neg_zero]
  Int.lt_of_neg_lt_neg this

protected theorem le_neg_of_le_neg {a b : Int} (h : a ≤ -b) : b ≤ -a := by
  have h := Int.neg_le_neg h
  rwa [Int.neg_neg] at h

protected theorem neg_le_of_neg_le {a b : Int} (h : -a ≤ b) : -b ≤ a := by
  have h := Int.neg_le_neg h
  rwa [Int.neg_neg] at h

protected theorem lt_neg_of_lt_neg {a b : Int} (h : a < -b) : b < -a := by
  have h := Int.neg_lt_neg h
  rwa [Int.neg_neg] at h

protected theorem neg_lt_of_neg_lt {a b : Int} (h : -a < b) : -b < a := by
  have h := Int.neg_lt_neg h
  rwa [Int.neg_neg] at h

protected theorem sub_nonpos_of_le {a b : Int} (h : a ≤ b) : a - b ≤ 0 := by
  have h := Int.add_le_add_right h (-b)
  rwa [Int.add_right_neg] at h

protected theorem le_of_sub_nonpos {a b : Int} (h : a - b ≤ 0) : a ≤ b := by
  have h := Int.add_le_add_right h b
  rwa [Int.sub_add_cancel, Int.zero_add] at h

protected theorem sub_neg_of_lt {a b : Int} (h : a < b) : a - b < 0 := by
  have h := Int.add_lt_add_right h (-b)
  rwa [Int.add_right_neg] at h

protected theorem lt_of_sub_neg {a b : Int} (h : a - b < 0) : a < b := by
  have h := Int.add_lt_add_right h b
  rwa [Int.sub_add_cancel, Int.zero_add] at h

protected theorem add_le_of_le_neg_add {a b c : Int} (h : b ≤ -a + c) : a + b ≤ c := by
  have h := Int.add_le_add_left h a
  rwa [Int.add_neg_cancel_left] at h

protected theorem le_neg_add_of_add_le {a b c : Int} (h : a + b ≤ c) : b ≤ -a + c := by
  have h := Int.add_le_add_left h (-a)
  rwa [Int.neg_add_cancel_left] at h

protected theorem add_le_of_le_sub_left {a b c : Int} (h : b ≤ c - a) : a + b ≤ c := by
  have h := Int.add_le_add_left h a
  rwa [← Int.add_sub_assoc, Int.add_comm a c, Int.add_sub_cancel] at h

protected theorem le_sub_left_of_add_le {a b c : Int} (h : a + b ≤ c) : b ≤ c - a := by
  have h := Int.add_le_add_right h (-a)
  rwa [Int.add_comm a b, Int.add_neg_cancel_right] at h

protected theorem add_le_of_le_sub_right {a b c : Int} (h : a ≤ c - b) : a + b ≤ c := by
  have h := Int.add_le_add_right h b
  rwa [Int.sub_add_cancel] at h

protected theorem le_sub_right_of_add_le {a b c : Int} (h : a + b ≤ c) : a ≤ c - b := by
  have h := Int.add_le_add_right h (-b)
  rwa [Int.add_neg_cancel_right] at h

protected theorem le_add_of_neg_add_le {a b c : Int} (h : -b + a ≤ c) : a ≤ b + c := by
  have h := Int.add_le_add_left h b
  rwa [Int.add_neg_cancel_left] at h

protected theorem neg_add_le_of_le_add {a b c : Int} (h : a ≤ b + c) : -b + a ≤ c := by
  have h := Int.add_le_add_left h (-b)
  rwa [Int.neg_add_cancel_left] at h

protected theorem le_add_of_sub_left_le {a b c : Int} (h : a - b ≤ c) : a ≤ b + c := by
  have h := Int.add_le_add_right h b
  rwa [Int.sub_add_cancel, Int.add_comm] at h

protected theorem le_add_of_sub_right_le {a b c : Int} (h : a - c ≤ b) : a ≤ b + c := by
  have h := Int.add_le_add_right h c
  rwa [Int.sub_add_cancel] at h

protected theorem sub_right_le_of_le_add {a b c : Int} (h : a ≤ b + c) : a - c ≤ b := by
  have h := Int.add_le_add_right h (-c)
  rwa [Int.add_neg_cancel_right] at h

protected theorem le_add_of_neg_add_le_left {a b c : Int} (h : -b + a ≤ c) : a ≤ b + c := by
  rw [Int.add_comm] at h
  exact Int.le_add_of_sub_left_le h

protected theorem neg_add_le_left_of_le_add {a b c : Int} (h : a ≤ b + c) : -b + a ≤ c := by
  rw [Int.add_comm]
  exact Int.sub_left_le_of_le_add h

protected theorem le_add_of_neg_add_le_right {a b c : Int} (h : -c + a ≤ b) : a ≤ b + c := by
  rw [Int.add_comm] at h
  exact Int.le_add_of_sub_right_le h

protected theorem neg_add_le_right_of_le_add {a b c : Int} (h : a ≤ b + c) : -c + a ≤ b := by
  rw [Int.add_comm] at h
  exact Int.neg_add_le_left_of_le_add h

protected theorem le_add_of_neg_le_sub_left {a b c : Int} (h : -a ≤ b - c) : c ≤ a + b :=
  Int.le_add_of_neg_add_le_left (Int.add_le_of_le_sub_right h)

protected theorem neg_le_sub_left_of_le_add {a b c : Int} (h : c ≤ a + b) : -a ≤ b - c := by
  have h := Int.le_neg_add_of_add_le (Int.sub_left_le_of_le_add h)
  rwa [Int.add_comm] at h

protected theorem le_add_of_neg_le_sub_right {a b c : Int} (h : -b ≤ a - c) : c ≤ a + b :=
  Int.le_add_of_sub_right_le (Int.add_le_of_le_sub_left h)

protected theorem neg_le_sub_right_of_le_add {a b c : Int} (h : c ≤ a + b) : -b ≤ a - c :=
  Int.le_sub_left_of_add_le (Int.sub_right_le_of_le_add h)

protected theorem sub_le_of_sub_le {a b c : Int} (h : a - b ≤ c) : a - c ≤ b :=
  Int.sub_left_le_of_le_add (Int.le_add_of_sub_right_le h)

protected theorem sub_le_sub_left {a b : Int} (h : a ≤ b) (c : Int) : c - b ≤ c - a :=
  Int.add_le_add_left (Int.neg_le_neg h) c

protected theorem sub_le_sub_right {a b : Int} (h : a ≤ b) (c : Int) : a - c ≤ b - c :=
  Int.add_le_add_right h (-c)

protected theorem sub_le_sub {a b c d : Int} (hab : a ≤ b) (hcd : c ≤ d) : a - d ≤ b - c :=
  Int.add_le_add hab (Int.neg_le_neg hcd)

protected theorem add_lt_of_lt_neg_add {a b c : Int} (h : b < -a + c) : a + b < c := by
  have h := Int.add_lt_add_left h a
  rwa [Int.add_neg_cancel_left] at h

protected theorem lt_neg_add_of_add_lt {a b c : Int} (h : a + b < c) : b < -a + c := by
  have h := Int.add_lt_add_left h (-a)
  rwa [Int.neg_add_cancel_left] at h

protected theorem add_lt_of_lt_sub_left {a b c : Int} (h : b < c - a) : a + b < c := by
  have h := Int.add_lt_add_left h a
  rwa [← Int.add_sub_assoc, Int.add_comm a c, Int.add_sub_cancel] at h

protected theorem lt_sub_left_of_add_lt {a b c : Int} (h : a + b < c) : b < c - a := by
  have h := Int.add_lt_add_right h (-a)
  rwa [Int.add_comm a b, Int.add_neg_cancel_right] at h

protected theorem add_lt_of_lt_sub_right {a b c : Int} (h : a < c - b) : a + b < c := by
  have h := Int.add_lt_add_right h b
  rwa [Int.sub_add_cancel] at h

protected theorem lt_sub_right_of_add_lt {a b c : Int} (h : a + b < c) : a < c - b := by
  have h := Int.add_lt_add_right h (-b)
  rwa [Int.add_neg_cancel_right] at h

protected theorem lt_add_of_neg_add_lt {a b c : Int} (h : -b + a < c) : a < b + c := by
  have h := Int.add_lt_add_left h b
  rwa [Int.add_neg_cancel_left] at h

protected theorem neg_add_lt_of_lt_add {a b c : Int} (h : a < b + c) : -b + a < c := by
  have h := Int.add_lt_add_left h (-b)
  rwa [Int.neg_add_cancel_left] at h

protected theorem lt_add_of_sub_left_lt {a b c : Int} (h : a - b < c) : a < b + c := by
  have h := Int.add_lt_add_right h b
  rwa [Int.sub_add_cancel, Int.add_comm] at h

protected theorem sub_left_lt_of_lt_add {a b c : Int} (h : a < b + c) : a - b < c := by
  have h := Int.add_lt_add_right h (-b)
  rwa [Int.add_comm b c, Int.add_neg_cancel_right] at h

protected theorem lt_add_of_sub_right_lt {a b c : Int} (h : a - c < b) : a < b + c := by
  have h := Int.add_lt_add_right h c
  rwa [Int.sub_add_cancel] at h

protected theorem sub_right_lt_of_lt_add {a b c : Int} (h : a < b + c) : a - c < b := by
  have h := Int.add_lt_add_right h (-c)
  rwa [Int.add_neg_cancel_right] at h

protected theorem lt_add_of_neg_add_lt_left {a b c : Int} (h : -b + a < c) : a < b + c := by
  rw [Int.add_comm] at h
  exact Int.lt_add_of_sub_left_lt h

protected theorem neg_add_lt_left_of_lt_add {a b c : Int} (h : a < b + c) : -b + a < c := by
  rw [Int.add_comm]
  exact Int.sub_left_lt_of_lt_add h

protected theorem lt_add_of_neg_add_lt_right {a b c : Int} (h : -c + a < b) : a < b + c := by
  rw [Int.add_comm] at h
  exact Int.lt_add_of_sub_right_lt h

protected theorem neg_add_lt_right_of_lt_add {a b c : Int} (h : a < b + c) : -c + a < b := by
  rw [Int.add_comm] at h
  exact Int.neg_add_lt_left_of_lt_add h

protected theorem lt_add_of_neg_lt_sub_left {a b c : Int} (h : -a < b - c) : c < a + b :=
  Int.lt_add_of_neg_add_lt_left (Int.add_lt_of_lt_sub_right h)

protected theorem neg_lt_sub_left_of_lt_add {a b c : Int} (h : c < a + b) : -a < b - c := by
  have h := Int.lt_neg_add_of_add_lt (Int.sub_left_lt_of_lt_add h)
  rwa [Int.add_comm] at h

protected theorem lt_add_of_neg_lt_sub_right {a b c : Int} (h : -b < a - c) : c < a + b :=
  Int.lt_add_of_sub_right_lt (Int.add_lt_of_lt_sub_left h)

protected theorem neg_lt_sub_right_of_lt_add {a b c : Int} (h : c < a + b) : -b < a - c :=
  Int.lt_sub_left_of_add_lt (Int.sub_right_lt_of_lt_add h)

protected theorem sub_lt_of_sub_lt {a b c : Int} (h : a - b < c) : a - c < b :=
  Int.sub_left_lt_of_lt_add (Int.lt_add_of_sub_right_lt h)

protected theorem sub_lt_sub_left {a b : Int} (h : a < b) (c : Int) : c - b < c - a :=
  Int.add_lt_add_left (Int.neg_lt_neg h) c

protected theorem sub_lt_sub_right {a b : Int} (h : a < b) (c : Int) : a - c < b - c :=
  Int.add_lt_add_right h (-c)

protected theorem sub_lt_sub {a b c d : Int} (hab : a < b) (hcd : c < d) : a - d < b - c :=
  Int.add_lt_add hab (Int.neg_lt_neg hcd)

protected theorem sub_lt_sub_of_le_of_lt {a b c d : Int}
  (hab : a ≤ b) (hcd : c < d) : a - d < b - c :=
  Int.add_lt_add_of_le_of_lt hab (Int.neg_lt_neg hcd)

protected theorem sub_lt_sub_of_lt_of_le {a b c d : Int}
  (hab : a < b) (hcd : c ≤ d) : a - d < b - c :=
  Int.add_lt_add_of_lt_of_le hab (Int.neg_le_neg hcd)

protected theorem add_le_add_three {a b c d e f : Int}
    (h₁ : a ≤ d) (h₂ : b ≤ e) (h₃ : c ≤ f) : a + b + c ≤ d + e + f :=
  Int.add_le_add (Int.add_le_add h₁ h₂) h₃

theorem exists_eq_neg_ofNat {a : Int} (H : a ≤ 0) : ∃ n : Nat, a = -(n : Int) :=
  let ⟨n, h⟩ := eq_ofNat_of_zero_le (Int.neg_nonneg_of_nonpos H)
  ⟨n, Int.eq_neg_of_eq_neg h.symm⟩

theorem lt_of_add_one_le {a b : Int} (H : a + 1 ≤ b) : a < b := H

theorem lt_add_one_of_le {a b : Int} (H : a ≤ b) : a < b + 1 := Int.add_le_add_right H 1

theorem le_of_lt_add_one {a b : Int} (H : a < b + 1) : a ≤ b := Int.le_of_add_le_add_right H

theorem sub_one_lt_of_le {a b : Int} (H : a ≤ b) : a - 1 < b :=
  Int.sub_right_lt_of_lt_add <| lt_add_one_of_le H

theorem le_of_sub_one_lt {a b : Int} (H : a - 1 < b) : a ≤ b :=
  le_of_lt_add_one <| Int.lt_add_of_sub_right_lt H

theorem le_sub_one_of_lt {a b : Int} (H : a < b) : a ≤ b - 1 := Int.le_sub_right_of_add_le H

theorem lt_of_le_sub_one {a b : Int} (H : a ≤ b - 1) : a < b := Int.add_le_of_le_sub_right H

/- ### Order properties and multiplication -/

protected theorem mul_lt_mul {a b c d : Int}
    (h₁ : a < c) (h₂ : b ≤ d) (h₃ : 0 < b) (h₄ : 0 ≤ c) : a * b < c * d :=
  Int.lt_of_lt_of_le (Int.mul_lt_mul_of_pos_right h₁ h₃) (Int.mul_le_mul_of_nonneg_left h₂ h₄)

protected theorem mul_lt_mul' {a b c d : Int}
    (h₁ : a ≤ c) (h₂ : b < d) (h₃ : 0 ≤ b) (h₄ : 0 < c) : a * b < c * d :=
  Int.lt_of_le_of_lt (Int.mul_le_mul_of_nonneg_right h₁ h₃) (Int.mul_lt_mul_of_pos_left h₂ h₄)

protected theorem mul_neg_of_pos_of_neg {a b : Int} (ha : 0 < a) (hb : b < 0) : a * b < 0 := by
  have h : a * b < a * 0 := Int.mul_lt_mul_of_pos_left hb ha
  rwa [Int.mul_zero] at h

protected theorem mul_neg_of_neg_of_pos {a b : Int} (ha : a < 0) (hb : 0 < b) : a * b < 0 := by
  have h : a * b < 0 * b := Int.mul_lt_mul_of_pos_right ha hb
  rwa [Int.zero_mul] at h

protected theorem mul_nonneg_of_nonpos_of_nonpos {a b : Int}
  (ha : a ≤ 0) (hb : b ≤ 0) : 0 ≤ a * b := by
  have : 0 * b ≤ a * b := Int.mul_le_mul_of_nonpos_right ha hb
  rwa [Int.zero_mul] at this

protected theorem mul_lt_mul_of_neg_left {a b c : Int} (h : b < a) (hc : c < 0) : c * a < c * b :=
  have : -c > 0 := Int.neg_pos_of_neg hc
  have : -c * b < -c * a := Int.mul_lt_mul_of_pos_left h this
  have : -(c * b) < -(c * a) := by
    rwa [← Int.neg_mul_eq_neg_mul, ← Int.neg_mul_eq_neg_mul] at this
  Int.lt_of_neg_lt_neg this

protected theorem mul_lt_mul_of_neg_right {a b c : Int} (h : b < a) (hc : c < 0) : a * c < b * c :=
  have : -c > 0 := Int.neg_pos_of_neg hc
  have : b * -c < a * -c := Int.mul_lt_mul_of_pos_right h this
  have : -(b * c) < -(a * c) := by
    rwa [← Int.neg_mul_eq_mul_neg, ← Int.neg_mul_eq_mul_neg] at this
  Int.lt_of_neg_lt_neg this

protected theorem mul_pos_of_neg_of_neg {a b : Int} (ha : a < 0) (hb : b < 0) : 0 < a * b := by
  have : 0 * b < a * b := Int.mul_lt_mul_of_neg_right ha hb
  rwa [Int.zero_mul] at this

protected theorem mul_self_le_mul_self {a b : Int} (h1 : 0 ≤ a) (h2 : a ≤ b) : a * a ≤ b * b :=
  Int.mul_le_mul h2 h2 h1 (Int.le_trans h1 h2)

protected theorem mul_self_lt_mul_self {a b : Int} (h1 : 0 ≤ a) (h2 : a < b) : a * a < b * b :=
  Int.mul_lt_mul' (Int.le_of_lt h2) h2 h1 (Int.lt_of_le_of_lt h1 h2)

/- ## sign -/

@[simp] theorem sign_zero : sign 0 = 0 := rfl
@[simp] theorem sign_one : sign 1 = 1 := rfl
theorem sign_neg_one : sign (-1) = -1 := rfl

@[simp] theorem sign_of_add_one (x : Nat) : Int.sign (x + 1) = 1 := rfl
@[simp] theorem sign_negSucc (x : Nat) : Int.sign (Int.negSucc x) = -1 := rfl

theorem natAbs_sign (z : Int) : z.sign.natAbs = if z = 0 then 0 else 1 :=
  match z with | 0 | succ _ | -[_+1] => rfl

theorem natAbs_sign_of_nonzero {z : Int} (hz : z ≠ 0) : z.sign.natAbs = 1 := by
  rw [Int.natAbs_sign, if_neg hz]

theorem sign_ofNat_of_nonzero {n : Nat} (hn : n ≠ 0) : Int.sign n = 1 :=
  match n, Nat.exists_eq_succ_of_ne_zero hn with
  | _, ⟨n, rfl⟩ => Int.sign_of_add_one n

@[simp] theorem sign_neg (z : Int) : Int.sign (-z) = -Int.sign z := by
  match z with | 0 | succ _ | -[_+1] => rfl

theorem sign_mul_natAbs : ∀ a : Int, sign a * natAbs a = a
  | 0      => rfl
  | succ _ => Int.one_mul _
  | -[_+1] => (Int.neg_eq_neg_one_mul _).symm

@[simp] theorem sign_mul : ∀ a b, sign (a * b) = sign a * sign b
  | a, 0 | 0, b => by simp [Int.mul_zero, Int.zero_mul]
  | succ _, succ _ | succ _, -[_+1] | -[_+1], succ _ | -[_+1], -[_+1] => rfl

theorem sign_eq_one_of_pos {a : Int} (h : 0 < a) : sign a = 1 :=
  match a, eq_succ_of_zero_lt h with
  | _, ⟨_, rfl⟩ => rfl

theorem sign_eq_neg_one_of_neg {a : Int} (h : a < 0) : sign a = -1 :=
  match a, eq_negSucc_of_lt_zero h with
  | _, ⟨_, rfl⟩ => rfl

theorem eq_zero_of_sign_eq_zero : ∀ {a : Int}, sign a = 0 → a = 0
  | 0, _ => rfl

theorem pos_of_sign_eq_one : ∀ {a : Int}, sign a = 1 → 0 < a
  | (_ + 1 : Nat), _ => ofNat_lt.2 (Nat.succ_pos _)

theorem neg_of_sign_eq_neg_one : ∀ {a : Int}, sign a = -1 → a < 0
  | (_ + 1 : Nat), h => nomatch h
  | 0, h => nomatch h
  | -[_+1], _ => negSucc_lt_zero _

theorem sign_eq_one_iff_pos (a : Int) : sign a = 1 ↔ 0 < a :=
  ⟨pos_of_sign_eq_one, sign_eq_one_of_pos⟩

theorem sign_eq_neg_one_iff_neg (a : Int) : sign a = -1 ↔ a < 0 :=
  ⟨neg_of_sign_eq_neg_one, sign_eq_neg_one_of_neg⟩

@[simp] theorem sign_eq_zero_iff_zero (a : Int) : sign a = 0 ↔ a = 0 :=
  ⟨eq_zero_of_sign_eq_zero, fun h => by rw [h, sign_zero]⟩

@[simp] theorem sign_sign : sign (sign x) = sign x := by
  match x with
  | 0 => rfl
  | .ofNat (_ + 1) => rfl
  | .negSucc _ => rfl

@[simp] theorem sign_nonneg : 0 ≤ sign x ↔ 0 ≤ x := by
  match x with
  | 0 => rfl
  | .ofNat (_ + 1) =>
    simp (config := { decide := true }) only [sign, true_iff]
    exact Int.le_add_one (ofNat_nonneg _)
  | .negSucc _ => simp (config := { decide := true }) [sign]

/- ## natAbs -/

theorem natAbs_ne_zero {a : Int} : a.natAbs ≠ 0 ↔ a ≠ 0 := not_congr Int.natAbs_eq_zero

theorem natAbs_mul_self : ∀ {a : Int}, ↑(natAbs a * natAbs a) = a * a
  | ofNat _ => rfl
  | -[_+1]  => rfl

theorem eq_nat_or_neg (a : Int) : ∃ n : Nat, a = n ∨ a = -↑n := ⟨_, natAbs_eq a⟩

theorem natAbs_mul_natAbs_eq {a b : Int} {c : Nat}
    (h : a * b = (c : Int)) : a.natAbs * b.natAbs = c := by rw [← natAbs_mul, h, natAbs]

@[simp] theorem natAbs_mul_self' (a : Int) : (natAbs a * natAbs a : Int) = a * a := by
  rw [← Int.ofNat_mul, natAbs_mul_self]

theorem natAbs_eq_iff {a : Int} {n : Nat} : a.natAbs = n ↔ a = n ∨ a = -↑n := by
  rw [← Int.natAbs_eq_natAbs_iff, Int.natAbs_ofNat]

@[deprecated] alias ofNat_natAbs_eq_of_nonneg := natAbs_of_nonneg

theorem natAbs_add_le (a b : Int) : natAbs (a + b) ≤ natAbs a + natAbs b := by
  suffices ∀ a b : Nat, natAbs (subNatNat a b.succ) ≤ (a + b).succ by
    match a, b with
    | (a:Nat), (b:Nat) => rw [ofNat_add_ofNat, natAbs_ofNat]; apply Nat.le_refl
    | (a:Nat), -[b+1]  => rw [natAbs_ofNat, natAbs_negSucc]; apply this
    | -[a+1],  (b:Nat) =>
      rw [natAbs_negSucc, natAbs_ofNat, Nat.succ_add, Nat.add_comm a b]; apply this
    | -[a+1],  -[b+1]  => rw [natAbs_negSucc, succ_add]; apply Nat.le_refl
  refine fun a b => subNatNat_elim a b.succ
    (fun m n i => n = b.succ → natAbs i ≤ (m + b).succ) ?_
    (fun i n (e : (n + i).succ = _) => ?_) rfl
  · rintro i n rfl
    rw [Nat.add_comm _ i, Nat.add_assoc]
    exact Nat.le_add_right i (b.succ + b).succ
  · apply succ_le_succ
    rw [← succ.inj e, ← Nat.add_assoc, Nat.add_comm]
    apply Nat.le_add_right

theorem natAbs_sub_le (a b : Int) : natAbs (a - b) ≤ natAbs a + natAbs b := by
  rw [← Int.natAbs_neg b]; apply natAbs_add_le

theorem negSucc_eq' (m : Nat) : -[m+1] = -m - 1 := by simp only [negSucc_eq, Int.neg_add]; rfl

theorem natAbs_lt_natAbs_of_nonneg_of_lt {a b : Int}
    (w₁ : 0 ≤ a) (w₂ : a < b) : a.natAbs < b.natAbs :=
  match a, b, eq_ofNat_of_zero_le w₁, eq_ofNat_of_zero_le (Int.le_trans w₁ (Int.le_of_lt w₂)) with
  | _, _, ⟨_, rfl⟩, ⟨_, rfl⟩ => ofNat_lt.1 w₂

theorem eq_natAbs_iff_mul_eq_zero : natAbs a = n ↔ (a - n) * (a + n) = 0 := by
  rw [natAbs_eq_iff, Int.mul_eq_zero, ← Int.sub_neg, Int.sub_eq_zero, Int.sub_eq_zero]

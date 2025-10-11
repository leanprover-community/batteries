/-
Copyright (c) 2023 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: François G. Dorais, Mario Carneiro
-/
import Batteries.Classes.Order

/-! ### UInt8 -/

@[ext] theorem UInt8.ext : {x y : UInt8} → x.toNat = y.toNat → x = y
  | ⟨⟨_,_⟩⟩, ⟨⟨_,_⟩⟩, rfl => rfl

@[simp] theorem UInt8.toUInt16_toNat (x : UInt8) : x.toUInt16.toNat = x.toNat := rfl

@[simp] theorem UInt8.toUInt32_toNat (x : UInt8) : x.toUInt32.toNat = x.toNat := rfl

@[simp] theorem UInt8.toUInt64_toNat (x : UInt8) : x.toUInt64.toNat = x.toNat := rfl

instance : Std.LawfulOrd UInt8 :=
  Std.LawfulCmp.compareOfLessAndEq_of_irrefl_of_trans_of_not_lt_of_antisymm
    (fun _ => Nat.lt_irrefl _) Nat.lt_trans Nat.not_lt UInt8.le_antisymm

theorem UInt8.le_iff_toNat_le_toNat {x y : UInt8} : x ≤ y ↔ x.toNat ≤ y.toNat := .rfl

theorem UInt8.lt_iff_toNat_lt_toNat {x y : UInt8} : x < y ↔ x.toNat < y.toNat := .rfl

theorem UInt8.compare_eq_toNat_compare_toNat (x y : UInt8) :
    compare x y = compare x.toNat y.toNat := by
  simp only [compare, compareOfLessAndEq, lt_iff_toNat_lt_toNat, UInt8.ext_iff]

theorem UInt8.max_def (x y : UInt8) : max x y = if x ≤ y then y else x := rfl

theorem UInt8.min_def (x y : UInt8) : min x y = if x ≤ y then x else y := rfl

theorem UInt8.toNat_max (x y : UInt8) : (max x y).toNat = max x.toNat y.toNat := by
  rw [max_def]
  split
  · next h =>
      rw [le_iff_toNat_le_toNat] at h
      rw [Nat.max_eq_right h]
  · next h =>
      rw [le_iff_toNat_le_toNat] at h
      rw [Nat.max_eq_left (Nat.le_of_not_ge h)]

theorem UInt8.toNat_min (x y : UInt8) : (min x y).toNat = min x.toNat y.toNat := by
  rw [min_def]
  split
  · next h =>
      rw [le_iff_toNat_le_toNat] at h
      rw [Nat.min_eq_left h]
  · next h =>
      rw [le_iff_toNat_le_toNat] at h
      rw [Nat.min_eq_right (Nat.le_of_not_ge h)]

/-! ### UInt16 -/

@[ext] theorem UInt16.ext : {x y : UInt16} → x.toNat = y.toNat → x = y
  | ⟨⟨_,_⟩⟩, ⟨⟨_,_⟩⟩, rfl => rfl

@[simp] theorem UInt16.toUInt8_toNat (x : UInt16) : x.toUInt8.toNat = x.toNat % 2 ^ 8 := rfl

@[simp] theorem UInt16.toUInt32_toNat (x : UInt16) : x.toUInt32.toNat = x.toNat := rfl

@[simp] theorem UInt16.toUInt64_toNat (x : UInt16) : x.toUInt64.toNat = x.toNat := rfl

instance : Std.LawfulOrd UInt16 :=
  Std.LawfulCmp.compareOfLessAndEq_of_irrefl_of_trans_of_not_lt_of_antisymm
    (fun _ => Nat.lt_irrefl _) Nat.lt_trans Nat.not_lt UInt16.le_antisymm

theorem UInt16.le_iff_toNat_le_toNat {x y : UInt16} : x ≤ y ↔ x.toNat ≤ y.toNat := .rfl

theorem UInt16.lt_iff_toNat_lt_toNat {x y : UInt16} : x < y ↔ x.toNat < y.toNat := .rfl

theorem UInt16.compare_eq_toNat_compare_toNat (x y : UInt16) :
    compare x y = compare x.toNat y.toNat := by
  simp only [compare, compareOfLessAndEq, lt_iff_toNat_lt_toNat, UInt16.ext_iff]

theorem UInt16.max_def (x y : UInt16) : max x y = if x ≤ y then y else x := rfl

theorem UInt16.min_def (x y : UInt16) : min x y = if x ≤ y then x else y := rfl

theorem UInt16.toNat_max (x y : UInt16) : (max x y).toNat = max x.toNat y.toNat := by
  rw [max_def]
  split
  · next h =>
      rw [le_iff_toNat_le_toNat] at h
      rw [Nat.max_eq_right h]
  · next h =>
      rw [le_iff_toNat_le_toNat] at h
      rw [Nat.max_eq_left (Nat.le_of_not_ge h)]

theorem UInt16.toNat_min (x y : UInt16) : (min x y).toNat = min x.toNat y.toNat := by
  rw [min_def]
  split
  · next h =>
      rw [le_iff_toNat_le_toNat] at h
      rw [Nat.min_eq_left h]
  · next h =>
      rw [le_iff_toNat_le_toNat] at h
      rw [Nat.min_eq_right (Nat.le_of_not_ge h)]

/-! ### UInt32 -/

@[ext] theorem UInt32.ext : {x y : UInt32} → x.toNat = y.toNat → x = y
  | ⟨⟨_,_⟩⟩, ⟨⟨_,_⟩⟩, rfl => rfl

@[simp] theorem UInt32.toUInt8_toNat (x : UInt32) : x.toUInt8.toNat = x.toNat % 2 ^ 8 := rfl

@[simp] theorem UInt32.toUInt16_toNat (x : UInt32) : x.toUInt16.toNat = x.toNat % 2 ^ 16 := rfl

@[simp] theorem UInt32.toUInt64_toNat (x : UInt32) : x.toUInt64.toNat = x.toNat := rfl

instance : Std.LawfulOrd UInt32 :=
  Std.LawfulCmp.compareOfLessAndEq_of_irrefl_of_trans_of_not_lt_of_antisymm
    (fun _ => Nat.lt_irrefl _) Nat.lt_trans Nat.not_lt UInt32.le_antisymm

theorem UInt32.le_iff_toNat_le_toNat {x y : UInt32} : x ≤ y ↔ x.toNat ≤ y.toNat := .rfl

theorem UInt32.lt_iff_toNat_lt_toNat {x y : UInt32} : x < y ↔ x.toNat < y.toNat := .rfl

theorem UInt32.compare_eq_toNat_compare_toNat (x y : UInt32) :
    compare x y = compare x.toNat y.toNat := by
  simp only [compare, compareOfLessAndEq, lt_iff_toNat_lt_toNat, UInt32.ext_iff]

theorem UInt32.max_def (x y : UInt32) : max x y = if x ≤ y then y else x := rfl

theorem UInt32.min_def (x y : UInt32) : min x y = if x ≤ y then x else y := rfl

theorem UInt32.toNat_max (x y : UInt32) : (max x y).toNat = max x.toNat y.toNat := by
  rw [max_def]
  split
  · next h =>
      rw [le_iff_toNat_le_toNat] at h
      rw [Nat.max_eq_right h]
  · next h =>
      rw [le_iff_toNat_le_toNat] at h
      rw [Nat.max_eq_left (Nat.le_of_not_ge h)]

theorem UInt32.toNat_min (x y : UInt32) : (min x y).toNat = min x.toNat y.toNat := by
  rw [min_def]
  split
  · next h =>
      rw [le_iff_toNat_le_toNat] at h
      rw [Nat.min_eq_left h]
  · next h =>
      rw [le_iff_toNat_le_toNat] at h
      rw [Nat.min_eq_right (Nat.le_of_not_ge h)]

/-! ### UInt64 -/

@[ext] theorem UInt64.ext : {x y : UInt64} → x.toNat = y.toNat → x = y
  | ⟨⟨_,_⟩⟩, ⟨⟨_,_⟩⟩, rfl => rfl

@[simp] theorem UInt64.toUInt8_toNat (x : UInt64) : x.toUInt8.toNat = x.toNat % 2 ^ 8 := rfl

@[simp] theorem UInt64.toUInt16_toNat (x : UInt64) : x.toUInt16.toNat = x.toNat % 2 ^ 16 := rfl

@[simp] theorem UInt64.toUInt32_toNat (x : UInt64) : x.toUInt32.toNat = x.toNat % 2 ^ 32 := rfl

instance : Std.LawfulOrd UInt64 :=
  Std.LawfulCmp.compareOfLessAndEq_of_irrefl_of_trans_of_not_lt_of_antisymm
    (fun _ => Nat.lt_irrefl _) Nat.lt_trans Nat.not_lt UInt64.le_antisymm

theorem UInt64.le_iff_toNat_le_toNat {x y : UInt64} : x ≤ y ↔ x.toNat ≤ y.toNat := .rfl

theorem UInt64.lt_iff_toNat_lt_toNat {x y : UInt64} : x < y ↔ x.toNat < y.toNat := .rfl

theorem UInt64.compare_eq_toNat_compare_toNat (x y : UInt64) :
    compare x y = compare x.toNat y.toNat := by
  simp only [compare, compareOfLessAndEq, lt_iff_toNat_lt_toNat, UInt64.ext_iff]

theorem UInt64.max_def (x y : UInt64) : max x y = if x ≤ y then y else x := rfl

theorem UInt64.min_def (x y : UInt64) : min x y = if x ≤ y then x else y := rfl

theorem UInt64.toNat_max (x y : UInt64) : (max x y).toNat = max x.toNat y.toNat := by
  rw [max_def]
  split
  · next h =>
      rw [le_iff_toNat_le_toNat] at h
      rw [Nat.max_eq_right h]
  · next h =>
      rw [le_iff_toNat_le_toNat] at h
      rw [Nat.max_eq_left (Nat.le_of_not_ge h)]

theorem UInt64.toNat_min (x y : UInt64) : (min x y).toNat = min x.toNat y.toNat := by
  rw [min_def]
  split
  · next h =>
      rw [le_iff_toNat_le_toNat] at h
      rw [Nat.min_eq_left h]
  · next h =>
      rw [le_iff_toNat_le_toNat] at h
      rw [Nat.min_eq_right (Nat.le_of_not_ge h)]

/-! ### USize -/

@[ext] theorem USize.ext : {x y : USize} → x.toNat = y.toNat → x = y
  | ⟨⟨_,_⟩⟩, ⟨⟨_,_⟩⟩, rfl => rfl

theorem USize.toUInt64_toNat (x : USize) : x.toUInt64.toNat = x.toNat := by simp

theorem UInt32.toUSize_toNat (x : UInt32) : x.toUSize.toNat = x.toNat := by simp

instance : Std.LawfulOrd USize :=
  Std.LawfulCmp.compareOfLessAndEq_of_irrefl_of_trans_of_not_lt_of_antisymm
    (fun _ => Nat.lt_irrefl _) Nat.lt_trans Nat.not_lt USize.le_antisymm

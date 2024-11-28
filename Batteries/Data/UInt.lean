/-
Copyright (c) 2023 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: François G. Dorais, Mario Carneiro
-/
import Batteries.Classes.Order

/-! ### UInt8 -/

@[ext] theorem UInt8.ext : {x y : UInt8} → x.toNat = y.toNat → x = y
  | ⟨⟨_,_⟩⟩, ⟨⟨_,_⟩⟩, rfl => rfl

theorem UInt8.toNat_lt (x : UInt8) : x.toNat < 2 ^ 8 := x.val.isLt

@[deprecated UInt8.toNat_toUInt16 (since := "2024-11-28")]
theorem UInt8.toUInt16_toNat (x : UInt8) : x.toUInt16.toNat = x.toNat := rfl

@[deprecated UInt8.toNat_toUInt32 (since := "2024-11-28")]
theorem UInt8.toUInt32_toNat (x : UInt8) : x.toUInt32.toNat = x.toNat := rfl

@[deprecated UInt8.toNat_toUInt64 (since := "2024-11-28")]
theorem UInt8.toUInt64_toNat (x : UInt8) : x.toUInt64.toNat = x.toNat := rfl

instance : Batteries.LawfulOrd UInt8 := .compareOfLessAndEq
  (fun _ => Nat.lt_irrefl _) Nat.lt_trans Nat.not_lt UInt8.le_antisymm

/-! ### UInt16 -/

@[ext] theorem UInt16.ext : {x y : UInt16} → x.toNat = y.toNat → x = y
  | ⟨⟨_,_⟩⟩, ⟨⟨_,_⟩⟩, rfl => rfl

theorem UInt16.toNat_lt (x : UInt16) : x.toNat < 2 ^ 16 := x.val.isLt

@[deprecated UInt16.toNat_toUInt8 (since := "2024-11-28")]
theorem UInt16.toUInt8_toNat (x : UInt16) : x.toUInt8.toNat = x.toNat % 2 ^ 8 := rfl

@[deprecated UInt16.toNat_toUInt32 (since := "2024-11-28")]
theorem UInt16.toUInt32_toNat (x : UInt16) : x.toUInt32.toNat = x.toNat := rfl

@[deprecated UInt16.toNat_toUInt64 (since := "2024-11-28")]
theorem UInt16.toUInt64_toNat (x : UInt16) : x.toUInt64.toNat = x.toNat := rfl

instance : Batteries.LawfulOrd UInt16 := .compareOfLessAndEq
  (fun _ => Nat.lt_irrefl _) Nat.lt_trans Nat.not_lt UInt16.le_antisymm

/-! ### UInt32 -/

@[ext] theorem UInt32.ext : {x y : UInt32} → x.toNat = y.toNat → x = y
  | ⟨⟨_,_⟩⟩, ⟨⟨_,_⟩⟩, rfl => rfl

theorem UInt32.toNat_lt (x : UInt32) : x.toNat < 2 ^ 32 := x.val.isLt

@[deprecated UInt32.toNat_toUInt8 (since := "2024-11-28")]
theorem UInt32.toUInt8_toNat (x : UInt32) : x.toUInt8.toNat = x.toNat % 2 ^ 8 := rfl

@[deprecated UInt32.toNat_toUInt16 (since := "2024-11-28")]
theorem UInt32.toUInt16_toNat (x : UInt32) : x.toUInt16.toNat = x.toNat % 2 ^ 16 := rfl

@[deprecated UInt32.toNat_toUInt64 (since := "2024-11-28")]
theorem UInt32.toUInt64_toNat (x : UInt32) : x.toUInt64.toNat = x.toNat := rfl

instance : Batteries.LawfulOrd UInt32 := .compareOfLessAndEq
  (fun _ => Nat.lt_irrefl _) Nat.lt_trans Nat.not_lt UInt32.le_antisymm

/-! ### UInt64 -/

@[ext] theorem UInt64.ext : {x y : UInt64} → x.toNat = y.toNat → x = y
  | ⟨⟨_,_⟩⟩, ⟨⟨_,_⟩⟩, rfl => rfl

theorem UInt64.toNat_lt (x : UInt64) : x.toNat < 2 ^ 64 := x.val.isLt

@[deprecated UInt64.toNat_toUInt8 (since := "2024-11-28")]
theorem UInt64.toUInt8_toNat (x : UInt64) : x.toUInt8.toNat = x.toNat % 2 ^ 8 := rfl

@[deprecated UInt64.toNat_toUInt16 (since := "2024-11-28")]
theorem UInt64.toUInt16_toNat (x : UInt64) : x.toUInt16.toNat = x.toNat % 2 ^ 16 := rfl

@[deprecated UInt64.toNat_toUInt32 (since := "2024-11-28")]
theorem UInt64.toUInt32_toNat (x : UInt64) : x.toUInt32.toNat = x.toNat % 2 ^ 32 := rfl

instance : Batteries.LawfulOrd UInt64 := .compareOfLessAndEq
  (fun _ => Nat.lt_irrefl _) Nat.lt_trans Nat.not_lt UInt64.le_antisymm

/-! ### USize -/

@[ext] theorem USize.ext : {x y : USize} → x.toNat = y.toNat → x = y
  | ⟨⟨_,_⟩⟩, ⟨⟨_,_⟩⟩, rfl => rfl

theorem USize.size_eq : USize.size = 2 ^ System.Platform.numBits := by
  rw [USize.size]

theorem USize.le_size : 2 ^ 32 ≤ USize.size := le_usize_size

theorem USize.size_le : USize.size ≤ 2 ^ 64 := usize_size_le

theorem USize.toNat_lt (x : USize) : x.toNat < 2 ^ System.Platform.numBits := by
  rw [←USize.size_eq]; exact x.val.isLt

@[deprecated USize.toNat_toUInt64 (since := "2024-11-28")]
theorem USize.toUInt64_toNat (x : USize) : x.toUInt64.toNat = x.toNat := by
  simp only [USize.toUInt64, UInt64.toNat]; rfl

@[deprecated UInt32.toNat_toUSize (since := "2024-11-28")]
theorem UInt32.toUSize_toNat (x : UInt32) : x.toUSize.toNat = x.toNat := rfl

instance : Batteries.LawfulOrd USize := .compareOfLessAndEq
  (fun _ => Nat.lt_irrefl _) Nat.lt_trans Nat.not_lt USize.le_antisymm

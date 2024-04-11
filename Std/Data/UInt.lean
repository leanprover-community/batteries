/-
Copyright (c) 2023 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: François G. Dorais, Mario Carneiro
-/
import Std.Classes.Order

/-! ### UInt8 -/

@[ext] theorem UInt8.ext : {x y : UInt8} → x.toNat = y.toNat → x = y
  | ⟨⟨_,_⟩⟩, ⟨⟨_,_⟩⟩, rfl => rfl

theorem UInt8.ext_iff {x y : UInt8} : x = y ↔ x.toNat = y.toNat := ⟨congrArg _, UInt8.ext⟩

@[simp] theorem UInt8.val_val_eq_toNat (x : UInt8) : x.val.val = x.toNat := rfl

theorem UInt8.toNat_lt (x : UInt8) : x.toNat < 2 ^ 8 := x.val.isLt

@[simp] theorem UInt8.toUInt16_toNat (x : UInt8) : x.toUInt16.toNat = x.toNat :=
  Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le x.toNat_lt (by decide))

@[simp] theorem UInt8.toUInt32_toNat (x : UInt8) : x.toUInt32.toNat = x.toNat :=
  Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le x.toNat_lt (by decide))

@[simp] theorem UInt8.toUInt64_toNat (x : UInt8) : x.toUInt64.toNat = x.toNat :=
  Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le x.toNat_lt (by decide))

theorem UInt8.le_antisymm_iff {x y : UInt8} : x = y ↔ x ≤ y ∧ y ≤ x :=
  UInt8.ext_iff.trans Nat.le_antisymm_iff

theorem UInt8.le_antisymm {x y : UInt8} (h1 : x ≤ y) (h2 : y ≤ x) : x = y :=
  UInt8.le_antisymm_iff.2 ⟨h1, h2⟩

/-! ### UInt16 -/

@[ext] theorem UInt16.ext : {x y : UInt16} → x.toNat = y.toNat → x = y
  | ⟨⟨_,_⟩⟩, ⟨⟨_,_⟩⟩, rfl => rfl

theorem UInt16.ext_iff {x y : UInt16} : x = y ↔ x.toNat = y.toNat := ⟨congrArg _, UInt16.ext⟩

theorem UInt16.toNat_lt (x : UInt16) : x.toNat < 2 ^ 16 := x.val.isLt

@[simp] theorem UInt16.val_val_eq_toNat (x : UInt16) : x.val.val = x.toNat := rfl

@[simp] theorem UInt16.toUInt8_toNat (x : UInt16) : x.toUInt8.toNat = x.toNat % 2 ^ 8 := rfl

@[simp] theorem UInt16.toUInt32_toNat (x : UInt16) : x.toUInt32.toNat = x.toNat :=
  Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le x.toNat_lt (by decide))

@[simp] theorem UInt16.toUInt64_toNat (x : UInt16) : x.toUInt64.toNat = x.toNat :=
  Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le x.toNat_lt (by decide))

theorem UInt16.le_antisymm_iff {x y : UInt16} : x = y ↔ x ≤ y ∧ y ≤ x :=
  UInt16.ext_iff.trans Nat.le_antisymm_iff

theorem UInt16.le_antisymm {x y : UInt16} (h1 : x ≤ y) (h2 : y ≤ x) : x = y :=
  UInt16.le_antisymm_iff.2 ⟨h1, h2⟩

/-! ### UInt32 -/

@[ext] theorem UInt32.ext : {x y : UInt32} → x.toNat = y.toNat → x = y
  | ⟨⟨_,_⟩⟩, ⟨⟨_,_⟩⟩, rfl => rfl

theorem UInt32.ext_iff {x y : UInt32} : x = y ↔ x.toNat = y.toNat := ⟨congrArg _, UInt32.ext⟩

@[simp] theorem UInt32.val_val_eq_toNat (x : UInt32) : x.val.val = x.toNat := rfl

theorem UInt32.toNat_lt (x : UInt32) : x.toNat < 2 ^ 32 := x.val.isLt

@[simp] theorem UInt32.toUInt8_toNat (x : UInt32) : x.toUInt8.toNat = x.toNat % 2 ^ 8 := rfl

@[simp] theorem UInt32.toUInt16_toNat (x : UInt32) : x.toUInt16.toNat = x.toNat % 2 ^ 16 := rfl

@[simp] theorem UInt32.toUInt64_toNat (x : UInt32) : x.toUInt64.toNat = x.toNat :=
  Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le x.toNat_lt (by decide))

theorem UInt32.le_antisymm_iff {x y : UInt32} : x = y ↔ x ≤ y ∧ y ≤ x :=
  UInt32.ext_iff.trans Nat.le_antisymm_iff

theorem UInt32.le_antisymm {x y : UInt32} (h1 : x ≤ y) (h2 : y ≤ x) : x = y :=
  UInt32.le_antisymm_iff.2 ⟨h1, h2⟩

/-! ### UInt64 -/

@[ext] theorem UInt64.ext : {x y : UInt64} → x.toNat = y.toNat → x = y
  | ⟨⟨_,_⟩⟩, ⟨⟨_,_⟩⟩, rfl => rfl

theorem UInt64.ext_iff {x y : UInt64} : x = y ↔ x.toNat = y.toNat := ⟨congrArg _, UInt64.ext⟩

@[simp] theorem UInt64.val_val_eq_toNat (x : UInt64) : x.val.val = x.toNat := rfl

theorem UInt64.toNat_lt (x : UInt64) : x.toNat < 2 ^ 64 := x.val.isLt

@[simp] theorem UInt64.toUInt8_toNat (x : UInt64) : x.toUInt8.toNat = x.toNat % 2 ^ 8 := rfl

@[simp] theorem UInt64.toUInt16_toNat (x : UInt64) : x.toUInt16.toNat = x.toNat % 2 ^ 16 := rfl

@[simp] theorem UInt64.toUInt32_toNat (x : UInt64) : x.toUInt32.toNat = x.toNat % 2 ^ 32 := rfl

theorem UInt64.le_antisymm_iff {x y : UInt64} : x = y ↔ x ≤ y ∧ y ≤ x :=
  UInt64.ext_iff.trans Nat.le_antisymm_iff

theorem UInt64.le_antisymm {x y : UInt64} (h1 : x ≤ y) (h2 : y ≤ x) : x = y :=
  UInt64.le_antisymm_iff.2 ⟨h1, h2⟩

/-! ### USize -/

@[ext] theorem USize.ext : {x y : USize} → x.toNat = y.toNat → x = y
  | ⟨⟨_,_⟩⟩, ⟨⟨_,_⟩⟩, rfl => rfl

theorem USize.ext_iff {x y : USize} : x = y ↔ x.toNat = y.toNat := ⟨congrArg _, USize.ext⟩

@[simp] theorem USize.val_val_eq_toNat (x : USize) : x.val.val = x.toNat := rfl

theorem USize.size_eq : USize.size = 2 ^ System.Platform.numBits := by
  have : 1 ≤ 2 ^ System.Platform.numBits := Nat.succ_le_of_lt (Nat.two_pow_pos _)
  rw [USize.size, Nat.succ_eq_add_one, Nat.sub_eq, Nat.sub_add_cancel this]

theorem USize.le_size : 2 ^ 32 ≤ USize.size := by
  rw [size_eq]
  apply Nat.pow_le_pow_of_le_right (by decide)
  cases System.Platform.numBits_eq <;> simp_arith [*]

theorem USize.size_le : USize.size ≤ 2 ^ 64 := by
  rw [size_eq]
  apply Nat.pow_le_pow_of_le_right (by decide)
  cases System.Platform.numBits_eq <;> simp_arith [*]

theorem USize.toNat_lt (x : USize) : x.toNat < 2 ^ System.Platform.numBits := by
  rw [←USize.size_eq]; exact x.val.isLt

@[simp] theorem USize.toUInt64_toNat (x : USize) : x.toUInt64.toNat = x.toNat := by
  simp only [USize.toUInt64, UInt64.toNat]; rfl

@[simp] theorem UInt32.toUSize_toNat (x : UInt32) : x.toUSize.toNat = x.toNat :=
  Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le x.toNat_lt USize.le_size)

theorem USize.le_antisymm_iff {x y : USize} : x = y ↔ x ≤ y ∧ y ≤ x :=
  USize.ext_iff.trans Nat.le_antisymm_iff

theorem USize.le_antisymm {x y : USize} (h1 : x ≤ y) (h2 : y ≤ x) : x = y :=
  USize.le_antisymm_iff.2 ⟨h1, h2⟩

instance : Std.TransOrd USize := .compareOfLessAndEq_of_le
  (fun _ => Nat.lt_irrefl _) Nat.lt_trans Nat.not_lt.1 USize.le_antisymm

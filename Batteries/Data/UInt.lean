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

instance : Batteries.LawfulOrd UInt8 := .compareOfLessAndEq
  (fun _ => Nat.lt_irrefl _) Nat.lt_trans Nat.not_lt UInt8.le_antisymm

/-! ### UInt16 -/

@[ext] theorem UInt16.ext : {x y : UInt16} → x.toNat = y.toNat → x = y
  | ⟨⟨_,_⟩⟩, ⟨⟨_,_⟩⟩, rfl => rfl

@[simp] theorem UInt16.toUInt8_toNat (x : UInt16) : x.toUInt8.toNat = x.toNat % 2 ^ 8 := rfl

@[simp] theorem UInt16.toUInt32_toNat (x : UInt16) : x.toUInt32.toNat = x.toNat := rfl

@[simp] theorem UInt16.toUInt64_toNat (x : UInt16) : x.toUInt64.toNat = x.toNat := rfl

instance : Batteries.LawfulOrd UInt16 := .compareOfLessAndEq
  (fun _ => Nat.lt_irrefl _) Nat.lt_trans Nat.not_lt UInt16.le_antisymm

/-! ### UInt32 -/

@[ext] theorem UInt32.ext : {x y : UInt32} → x.toNat = y.toNat → x = y
  | ⟨⟨_,_⟩⟩, ⟨⟨_,_⟩⟩, rfl => rfl

@[simp] theorem UInt32.toUInt8_toNat (x : UInt32) : x.toUInt8.toNat = x.toNat % 2 ^ 8 := rfl

@[simp] theorem UInt32.toUInt16_toNat (x : UInt32) : x.toUInt16.toNat = x.toNat % 2 ^ 16 := rfl

@[simp] theorem UInt32.toUInt64_toNat (x : UInt32) : x.toUInt64.toNat = x.toNat := rfl

instance : Batteries.LawfulOrd UInt32 := .compareOfLessAndEq
  (fun _ => Nat.lt_irrefl _) Nat.lt_trans Nat.not_lt UInt32.le_antisymm

/-! ### UInt64 -/

@[ext] theorem UInt64.ext : {x y : UInt64} → x.toNat = y.toNat → x = y
  | ⟨⟨_,_⟩⟩, ⟨⟨_,_⟩⟩, rfl => rfl

@[simp] theorem UInt64.toUInt8_toNat (x : UInt64) : x.toUInt8.toNat = x.toNat % 2 ^ 8 := rfl

@[simp] theorem UInt64.toUInt16_toNat (x : UInt64) : x.toUInt16.toNat = x.toNat % 2 ^ 16 := rfl

@[simp] theorem UInt64.toUInt32_toNat (x : UInt64) : x.toUInt32.toNat = x.toNat % 2 ^ 32 := rfl

instance : Batteries.LawfulOrd UInt64 := .compareOfLessAndEq
  (fun _ => Nat.lt_irrefl _) Nat.lt_trans Nat.not_lt UInt64.le_antisymm

/-! ### USize -/

@[ext] theorem USize.ext : {x y : USize} → x.toNat = y.toNat → x = y
  | ⟨⟨_,_⟩⟩, ⟨⟨_,_⟩⟩, rfl => rfl

@[simp] theorem USize.toUInt64_toNat (x : USize) : x.toUInt64.toNat = x.toNat := by
  simp only [USize.toUInt64, UInt64.toNat]; rfl

@[simp] theorem UInt32.toUSize_toNat (x : UInt32) : x.toUSize.toNat = x.toNat := rfl

instance : Batteries.LawfulOrd USize := .compareOfLessAndEq
  (fun _ => Nat.lt_irrefl _) Nat.lt_trans Nat.not_lt USize.le_antisymm

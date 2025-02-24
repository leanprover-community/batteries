/-
Copyright (c) 2023 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: François G. Dorais, Mario Carneiro
-/
import Batteries.Classes.Order

/-! ### UInt8 -/

@[ext] theorem UInt8.ext : {x y : UInt8} → x.toNat = y.toNat → x = y
  | ⟨⟨_,_⟩⟩, ⟨⟨_,_⟩⟩, rfl => rfl

instance : Batteries.LawfulOrd UInt8 := .compareOfLessAndEq
  (fun _ => Nat.lt_irrefl _) Nat.lt_trans Nat.not_lt UInt8.le_antisymm

/-! ### UInt16 -/

@[ext] theorem UInt16.ext : {x y : UInt16} → x.toNat = y.toNat → x = y
  | ⟨⟨_,_⟩⟩, ⟨⟨_,_⟩⟩, rfl => rfl

instance : Batteries.LawfulOrd UInt16 := .compareOfLessAndEq
  (fun _ => Nat.lt_irrefl _) Nat.lt_trans Nat.not_lt UInt16.le_antisymm

/-! ### UInt32 -/

@[ext] theorem UInt32.ext : {x y : UInt32} → x.toNat = y.toNat → x = y
  | ⟨⟨_,_⟩⟩, ⟨⟨_,_⟩⟩, rfl => rfl


instance : Batteries.LawfulOrd UInt32 := .compareOfLessAndEq
  (fun _ => Nat.lt_irrefl _) Nat.lt_trans Nat.not_lt UInt32.le_antisymm

/-! ### UInt64 -/

@[ext] theorem UInt64.ext : {x y : UInt64} → x.toNat = y.toNat → x = y
  | ⟨⟨_,_⟩⟩, ⟨⟨_,_⟩⟩, rfl => rfl

instance : Batteries.LawfulOrd UInt64 := .compareOfLessAndEq
  (fun _ => Nat.lt_irrefl _) Nat.lt_trans Nat.not_lt UInt64.le_antisymm

/-! ### USize -/

@[ext] theorem USize.ext : {x y : USize} → x.toNat = y.toNat → x = y
  | ⟨⟨_,_⟩⟩, ⟨⟨_,_⟩⟩, rfl => rfl

instance : Batteries.LawfulOrd USize := .compareOfLessAndEq
  (fun _ => Nat.lt_irrefl _) Nat.lt_trans Nat.not_lt USize.le_antisymm

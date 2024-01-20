import Std.Data.Nat.Init.Lemmas
import Std.Tactic.Ext.Attr

/-! ### UInt8 -/

@[ext] theorem UInt8.ext : {x y : UInt8} → x.toNat = y.toNat → x = y
  | ⟨⟨_,_⟩⟩, ⟨⟨_,_⟩⟩, rfl => rfl

@[simp] theorem UInt8.val_val_eq_toNat (x : UInt8) : x.val.val = x.toNat := rfl

theorem UInt8.toNat_lt (x : UInt8) : x.toNat < 2 ^ 8 := x.val.isLt

@[simp] theorem UInt8.toUInt16_toNat (x : UInt8) : x.toUInt16.toNat = x.toNat :=
  Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le x.toNat_lt (by decide))

@[simp] theorem UInt8.toUInt32_toNat (x : UInt8) : x.toUInt32.toNat = x.toNat :=
  Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le x.toNat_lt (by decide))

@[simp] theorem UInt8.toUInt64_toNat (x : UInt8) : x.toUInt64.toNat = x.toNat :=
  Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le x.toNat_lt (by decide))

/-! ### UInt16 -/

@[ext] theorem UInt16.ext : {x y : UInt16} → x.toNat = y.toNat → x = y
  | ⟨⟨_,_⟩⟩, ⟨⟨_,_⟩⟩, rfl => rfl

theorem UInt16.toNat_lt (x : UInt16) : x.toNat < 2 ^ 16 := x.val.isLt

@[simp] theorem UInt16.val_val_eq_toNat (x : UInt16) : x.val.val = x.toNat := rfl

@[simp] theorem UInt16.toUInt8_toNat (x : UInt16) : x.toUInt8.toNat = x.toNat % 2 ^ 8 := rfl

@[simp] theorem UInt16.toUInt32_toNat (x : UInt16) : x.toUInt32.toNat = x.toNat :=
  Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le x.toNat_lt (by decide))

@[simp] theorem UInt16.toUInt64_toNat (x : UInt16) : x.toUInt64.toNat = x.toNat :=
  Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le x.toNat_lt (by decide))

/-! ### UInt32 -/

@[ext] theorem UInt32.ext : {x y : UInt32} → x.toNat = y.toNat → x = y
  | ⟨⟨_,_⟩⟩, ⟨⟨_,_⟩⟩, rfl => rfl

@[simp] theorem UInt32.val_val_eq_toNat (x : UInt32) : x.val.val = x.toNat := rfl

theorem UInt32.toNat_lt (x : UInt32) : x.toNat < 2 ^ 32 := x.val.isLt

@[simp] theorem UInt32.toUInt8_toNat (x : UInt32) : x.toUInt8.toNat = x.toNat % 2 ^ 8 := rfl

@[simp] theorem UInt32.toUInt16_toNat (x : UInt32) : x.toUInt16.toNat = x.toNat % 2 ^ 16 := rfl

@[simp] theorem UInt32.toUInt64_toNat (x : UInt32) : x.toUInt64.toNat = x.toNat :=
  Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le x.toNat_lt (by decide))

/-! ### UInt64 -/

@[ext] theorem UInt64.ext : {x y : UInt64} → x.toNat = y.toNat → x = y
  | ⟨⟨_,_⟩⟩, ⟨⟨_,_⟩⟩, rfl => rfl

@[simp] theorem UInt64.val_val_eq_toNat (x : UInt64) : x.val.val = x.toNat := rfl

theorem UInt64.toNat_lt (x : UInt64) : x.toNat < 2 ^ 64 := x.val.isLt

@[simp] theorem UInt64.toUInt8_toNat (x : UInt64) : x.toUInt8.toNat = x.toNat % 2 ^ 8 := rfl

@[simp] theorem UInt64.toUInt16_toNat (x : UInt64) : x.toUInt16.toNat = x.toNat % 2 ^ 16 := rfl

@[simp] theorem UInt64.toUInt32_toNat (x : UInt64) : x.toUInt32.toNat = x.toNat % 2 ^ 32 := rfl

/-! ### USize -/

@[ext] theorem USize.ext : {x y : USize} → x.toNat = y.toNat → x = y
  | ⟨⟨_,_⟩⟩, ⟨⟨_,_⟩⟩, rfl => rfl

@[simp] theorem USize.val_val_eq_toNat (x : USize) : x.val.val = x.toNat := rfl

theorem USize.size_eq : USize.size = 2 ^ System.Platform.numBits := by
  have : 1 ≤ 2 ^ System.Platform.numBits := Nat.succ_le_of_lt (Nat.pow_two_pos _)
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

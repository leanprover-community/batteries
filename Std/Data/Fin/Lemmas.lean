/-
Copyright (c) 2022 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/

namespace Fin

@[simp] theorem ofNat'_zero_val : (Fin.ofNat' 0 h).val = 0 := Nat.zero_mod _

@[simp] theorem mod_val (a b : Fin n) : (a % b).val = a.val % b.val :=
  Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.mod_le ..) a.2)

@[simp] theorem div_val (a b : Fin n) : (a / b).val = a.val / b.val :=
  Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self ..) a.2)

@[simp] theorem modn_val (a : Fin n) (b : Nat) : (a.modn b).val = a.val % b :=
  Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.mod_le ..) a.2)

end Fin

namespace USize

@[simp] theorem lt_def {a b : USize} : a < b ↔ a.toNat < b.toNat := .rfl

@[simp] theorem le_def {a b : USize} : a ≤ b ↔ a.toNat ≤ b.toNat := .rfl

@[simp] theorem zero_toNat : (0 : USize).toNat = 0 := Nat.zero_mod _

@[simp] theorem mod_toNat (a b : USize) : (a % b).toNat = a.toNat % b.toNat :=
  Fin.mod_val ..

@[simp] theorem div_toNat (a b : USize) : (a / b).toNat = a.toNat / b.toNat :=
  Fin.div_val ..

@[simp] theorem modn_toNat (a : USize) (b : Nat) : (a.modn b).toNat = a.toNat % b :=
  Fin.modn_val ..

theorem mod_lt (a b : USize) (h : 0 < b) : a % b < b := USize.modn_lt _ (by simp at h; exact h)

theorem toNat.inj : ∀ {a b : USize}, a.toNat = b.toNat → a = b
  | ⟨_, _⟩, ⟨_, _⟩, rfl => rfl

end USize

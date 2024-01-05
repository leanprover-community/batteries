/-
Copyright (c) 2023 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: François G. Dorais
-/
import Std.Data.Array.Lemmas
import Std.Tactic.Ext.Attr

namespace ByteArray

@[ext] theorem ext : {a b : ByteArray} → a.data = b.data → a = b
  | ⟨_⟩, ⟨_⟩, rfl => rfl

/-! ### uget/uset -/

@[simp] theorem ugetElem_eq_getElem (a : ByteArray) {i : USize} (h : i.toNat < a.size) :
    a[i] = a[i.toNat] := rfl

@[simp] theorem uset_eq_set (a : ByteArray) {i : USize} (h : i.toNat < a.size) (v : UInt8) :
    a.uset i v h = a.set ⟨i.toNat, h⟩ v := rfl

/-! ### push -/

@[simp] theorem size_push (a : ByteArray) (b : UInt8) : (a.push b).size = a.size + 1 :=
  Array.size_push ..

@[simp] theorem get_push_eq (a : ByteArray) (x : UInt8) : (a.push x)[a.size] = x :=
  Array.get_push_eq ..

theorem get_push_lt (a : ByteArray) (x : UInt8) (i : Nat) (h : i < a.size) :
    (a.push x)[i]'(size_push .. ▸ Nat.lt_succ_of_lt h) = a[i] :=
  Array.get_push_lt ..

/-! ### set -/

@[simp] theorem size_set (a : ByteArray) (i : Fin a.size) (v : UInt8) :
    (a.set i v).size = a.size :=
  Array.size_set ..

@[simp] theorem get_set_eq (a : ByteArray) (i : Fin a.size) (v : UInt8) : (a.set i v)[i.val] = v :=
  Array.get_set_eq ..

theorem get_set_ne (a : ByteArray) (i : Fin a.size) (v : UInt8) (hj : j < a.size) (h : i.val ≠ j) :
    (a.set i v)[j]'(a.size_set .. ▸ hj) = a[j] :=
  Array.get_set_ne (h:=h) ..

theorem set_set (a : ByteArray) (i : Fin a.size) (v v' : UInt8) :
    (a.set i v).set ⟨i, by simp [i.2]⟩ v' = a.set i v' :=
  ByteArray.ext <| Array.set_set ..

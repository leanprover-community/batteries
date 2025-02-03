/-
Copyright (c) 2024 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas, François G. Dorais
-/

import Batteries.Data.Vector.Basic
import Batteries.Data.List.Basic
import Batteries.Data.List.Lemmas
import Batteries.Data.Array.Lemmas
import Batteries.Tactic.Lint.Simp

namespace Vector

theorem toArray_injective : ∀ {v w : Vector α n}, v.toArray = w.toArray → v = w
  | {..}, {..}, rfl => rfl


/-! ### mk lemmas -/

@[simp] theorem get_mk (a : Array α) (h : a.size = n) (i) :
    (Vector.mk a h).get i = a[i] := rfl

@[simp] theorem getD_mk (a : Array α) (h : a.size = n) (i x) :
    (Vector.mk a h).getD i x = a.getD i x := rfl

@[simp] theorem uget_mk (a : Array α) (h : a.size = n) (i) (hi : i.toNat < n) :
    (Vector.mk a h).uget i hi = a.uget i (by simp [h, hi]) := rfl

@[deprecated (since := "2024-11-25")] alias setN_mk := set_mk

@[deprecated (since := "2024-11-25")] alias swapN_mk := swap_mk

@[deprecated (since := "2024-11-25")] alias swapAtN_mk := swapAt_mk

/-! ### toArray lemmas -/

@[deprecated (since := "2024-11-25")] alias toArray_setD := toArray_setIfInBounds
@[deprecated (since := "2024-11-25")] alias toArray_setN := toArray_set
@[deprecated (since := "2024-11-25")] alias toArray_swap! := toArray_swapIfInBounds
@[deprecated (since := "2024-11-25")] alias toArray_swapN := toArray_swap
@[deprecated (since := "2024-11-25")] alias toArray_swapAtN := toArray_swapAt

theorem isEqv_eq_toArray_isEqv_toArray (a b : Vector α n) :
    a.isEqv b r = a.toArray.isEqv b.toArray r :=
  match a, b with | ⟨_,_⟩, ⟨_,_⟩ => mk_isEqv_mk ..

theorem beq_eq_toArray_beq [BEq α] (a b : Vector α n) : (a == b) = (a.toArray == b.toArray) := by
  simp [(· == ·), isEqv_eq_toArray_isEqv_toArray]

instance (α n) [BEq α] [LawfulBEq α] : LawfulBEq (Vector α n) where
  rfl {a} := by simp_all [beq_eq_toArray_beq]
  eq_of_beq {a b h} := by
    apply toArray_injective
    simp_all [beq_eq_toArray_beq]

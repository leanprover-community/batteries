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

/-! ### get lemmas -/

@[simp] theorem get_push_last (v : Vector α n) (a : α) :
    (v.push a).get (Fin.last n) = a :=
  getElem_push_last

@[simp] theorem get_push_castSucc (v : Vector α n) (a : α) (i : Fin n) :
    (v.push a).get (Fin.castSucc i) = v.get i :=
  getElem_push_lt _

@[simp] theorem get_map (v : Vector α n) (f : α → β) (i : Fin n) :
    (v.map f).get i = f (v.get i) :=
  getElem_map _ _

@[simp] theorem get_reverse (v : Vector α n) (i : Fin n) :
    v.reverse.get i = v.get (i.rev) :=
  getElem_reverse _ |>.trans <| congrArg v.get <| Fin.ext <| by simp; omega

@[simp] theorem get_replicate (n : Nat) (a : α) (i : Fin n) : (replicate n a).get i = a :=
  getElem_replicate _

@[simp] theorem get_range (n : Nat) (i : Fin n) : (range n).get i = i :=
  getElem_range _

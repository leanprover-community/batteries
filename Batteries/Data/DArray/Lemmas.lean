/-
Copyright (c) 2024 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: François G. Dorais
-/

import Batteries.Data.DArray.Basic

namespace Batteries.DArray

@[ext]
protected theorem ext : {a b : DArray n α} → (∀ i, a.get i = b.get i) → a = b
  | mk _, mk _, h => congrArg _ <| funext fun i => h i

@[simp]
theorem get_mk (i : Fin n) : DArray.get (.mk init) i = init i := rfl

theorem set_mk {α : Fin n → Type _} {init : (i : Fin n) → α i} (i : Fin n) (v : α i) :
    DArray.set (.mk init) i v = .mk fun j => if h : i = j then h ▸ v else init j := rfl

@[simp]
theorem get_set (a : DArray n α) (i : Fin n) (v : α i) : (a.set i v).get i = v := by
  simp only [DArray.get, DArray.set, dif_pos]

theorem get_set_ne (a : DArray n α) (v : α i) (h : i ≠ j) : (a.set i v).get j = a.get j := by
  simp only [DArray.get, DArray.set, dif_neg h]

@[simp]
theorem set_set (a : DArray n α) (i : Fin n) (v w : α i) : (a.set i v).set i w = a.set i w := by
  ext j
  if h : i = j then
    rw [← h, get_set, get_set]
  else
    rw [get_set_ne _ _ h, get_set_ne _ _ h, get_set_ne _ _ h]

theorem get_modifyF [Functor f] [LawfulFunctor f] (a : DArray n α) (i : Fin n) (t : α i → f (α i)) :
    (DArray.get . i) <$> a.modifyF i t = t (a.get i) := by
  simp [DArray.modifyF, ← comp_map]
  conv => rhs; rw [← id_map (t (a.get i))]
  congr; ext; simp

@[simp]
theorem get_modify (a : DArray n α) (i : Fin n) (t : α i → α i) :
    (a.modify i t).get i = t (a.get i) := get_modifyF (f:=Id) a i t

theorem get_modify_ne (a : DArray n α) (t : α i → α i) (h : i ≠ j) :
    (a.modify i t).get j = a.get j := get_set_ne _ _ h

@[simp]
theorem set_modify (a : DArray n α) (i : Fin n) (t : α i → α i) (v : α i) :
    (a.set i v).modify i t = a.set i (t v) := by
  ext j
  if h : i = j then
    cases h; simp
  else
    simp [h, get_modify_ne, get_set_ne]

@[simp]
theorem uget_eq_get (a : DArray n α) (i : USize) (h : i.toNat < n) :
    a.uget i h = a.get ⟨i.toNat, h⟩ := rfl

@[simp]
theorem uset_eq_set (a : DArray n α) (i : USize) (h : i.toNat < n) (v : α ⟨i.toNat, h⟩) :
    a.uset i h v = a.set ⟨i.toNat, h⟩ v := rfl

@[simp]
theorem umodifyF_eq_modifyF [Functor f] (a : DArray n α) (i : USize) (h : i.toNat < n)
    (t : α ⟨i.toNat, h⟩ → f (α ⟨i.toNat, h⟩)) : a.umodifyF i h t = a.modifyF ⟨i.toNat, h⟩ t := rfl

@[simp]
theorem umodify_eq_modify (a : DArray n α) (i : USize) (h : i.toNat < n)
    (t : α ⟨i.toNat, h⟩ → α ⟨i.toNat, h⟩) : a.umodify i h t = a.modify ⟨i.toNat, h⟩ t := rfl

@[simp]
theorem copy_eq (a : DArray n α) : a.copy = a := rfl

/-
Copyright (c) 2024 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: François G. Dorais
-/

import Batteries.Data.DArray.Basic

namespace Batteries.DArray

@[ext]
protected theorem ext : {a b : DArray n α} → (∀ i, a.fget i = b.fget i) → a = b
  | mk _, mk _, h => congrArg _ <| funext fun i => h i

@[simp]
theorem get_mk (i) (h : i < n) : DArray.get (.mk init) i = init ⟨i, h⟩ := rfl

@[simp]
theorem fget_mk (i : Fin n) : DArray.fget (.mk init) i = init i := rfl

theorem fset_mk {α : Fin n → Type _} {init : (i : Fin n) → α i} (i : Fin n) (v : α i) :
    DArray.fset (.mk init) i v = .mk fun j => if h : i = j then h ▸ v else init j := rfl

@[simp]
theorem fget_fset (a : DArray n α) (i : Fin n) (v : α i) : (a.fset i v).fget i = v := by
  simp only [DArray.fget, DArray.fset, dif_pos]

theorem fget_fset_ne (a : DArray n α) (v : α i) (h : i ≠ j) : (a.fset i v).fget j = a.fget j := by
  simp only [DArray.fget, DArray.fset, dif_neg h]; rfl

@[simp]
theorem fset_fset (a : DArray n α) (i : Fin n) (v w : α i) :
    (a.fset i v).fset i w = a.fset i w := by
  ext j
  if h : i = j then
    rw [← h, fget_fset, fget_fset]
  else
    rw [fget_fset_ne _ _ h, fget_fset_ne _ _ h, fget_fset_ne _ _ h]

theorem fget_modifyF [Functor f] [LawfulFunctor f] (a : DArray n α) (i : Fin n)
    (t : α i → f (α i)) : (DArray.fget . i) <$> a.modifyF i t = t (a.fget i) := by
  simp [DArray.modifyF]

@[simp]
theorem fget_modify (a : DArray n α) (i : Fin n) (t : α i → α i) :
    (a.modify i t).fget i = t (a.fget i) := fget_modifyF (f:=Id) a i t

theorem fget_modify_ne (a : DArray n α) (t : α i → α i) (h : i ≠ j) :
    (a.modify i t).fget j = a.fget j := fget_fset_ne _ _ h

@[simp]
theorem fset_modify (a : DArray n α) (i : Fin n) (t : α i → α i) (v : α i) :
    (a.fset i v).modify i t = a.fset i (t v) := by
  ext j
  if h : i = j then
    cases h; simp
  else
    simp [h, fget_modify_ne, fget_fset_ne]

@[simp]
theorem uget_eq_fget (a : DArray n α) (i : USize) (h : i.toNat < n) :
    a.uget i h = a.fget ⟨i.toNat, h⟩ := rfl

@[simp]
theorem uset_eq_fset (a : DArray n α) (i : USize) (h : i.toNat < n) (v : α ⟨i.toNat, h⟩) :
    a.uset i h v = a.fset ⟨i.toNat, h⟩ v := rfl

@[simp]
theorem umodifyF_eq_modifyF [Functor f] (a : DArray n α) (i : USize) (h : i.toNat < n)
    (t : α ⟨i.toNat, h⟩ → f (α ⟨i.toNat, h⟩)) : a.umodifyF i h t = a.modifyF ⟨i.toNat, h⟩ t := rfl

@[simp]
theorem umodify_eq_modify (a : DArray n α) (i : USize) (h : i.toNat < n)
    (t : α ⟨i.toNat, h⟩ → α ⟨i.toNat, h⟩) : a.umodify i h t = a.modify ⟨i.toNat, h⟩ t := rfl

@[simp]
theorem copy_eq (a : DArray n α) : a.copy = a := rfl

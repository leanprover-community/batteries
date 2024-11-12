/-
Copyright (c) 2022 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Batteries.Data.Fin.Basic
import Batteries.Data.List.Lemmas

namespace Fin

attribute [norm_cast] val_last

/-! ### clamp -/

@[simp] theorem coe_clamp (n m : Nat) : (clamp n m : Nat) = min n m := rfl

/-! ### enum/list -/

@[simp] theorem size_enum (n) : (enum n).size = n := Array.size_ofFn ..

@[simp] theorem enum_zero : (enum 0) = #[] := by simp [enum, Array.ofFn, Array.ofFn.go]

@[simp] theorem getElem_enum (i) (h : i < (enum n).size) : (enum n)[i] = ⟨i, size_enum n ▸ h⟩ :=
  Array.getElem_ofFn ..

@[simp] theorem length_list (n) : (list n).length = n := by simp [list]

@[simp] theorem getElem_list (i : Nat) (h : i < (list n).length) :
    (list n)[i] = cast (length_list n) ⟨i, h⟩ := by
  simp only [list]; rw [← Array.getElem_eq_getElem_toList, getElem_enum, cast_mk]

@[deprecated getElem_list (since := "2024-06-12")]
theorem get_list (i : Fin (list n).length) : (list n).get i = i.cast (length_list n) := by
  simp [getElem_list]

@[simp] theorem list_zero : list 0 = [] := by simp [list]

theorem list_succ (n) : list (n+1) = 0 :: (list n).map Fin.succ := by
  apply List.ext_get; simp; intro i; cases i <;> simp

theorem list_succ_last (n) : list (n+1) = (list n).map castSucc ++ [last n] := by
  rw [list_succ]
  induction n with
  | zero => simp
  | succ n ih =>
    rw [list_succ, List.map_cons castSucc, ih]
    simp [Function.comp_def, succ_castSucc]

theorem list_reverse (n) : (list n).reverse = (list n).map rev := by
  induction n with
  | zero => simp
  | succ n ih =>
    conv => lhs; rw [list_succ_last]
    conv => rhs; rw [list_succ]
    simp [← List.map_reverse, ih, Function.comp_def, rev_succ]

/-! ### foldlM -/

theorem foldlM_eq_foldlM_list [Monad m] (f : α → Fin n → m α) (x) :
    foldlM n f x = (list n).foldlM f x := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    rw [foldlM_succ, list_succ, List.foldlM_cons]
    congr; funext
    rw [List.foldlM_map, ih]

/-! ### foldrM -/

theorem foldrM_eq_foldrM_list [Monad m] [LawfulMonad m] (f : Fin n → α → m α) (x) :
    foldrM n f x = (list n).foldrM f x := by
  induction n with
  | zero => simp
  | succ n ih => rw [foldrM_succ, ih, list_succ, List.foldrM_cons, List.foldrM_map]

/-! ### foldl -/

theorem foldl_eq_foldl_list (f : α → Fin n → α) (x) : foldl n f x = (list n).foldl f x := by
  induction n generalizing x with
  | zero => rw [foldl_zero, list_zero, List.foldl_nil]
  | succ n ih => rw [foldl_succ, ih, list_succ, List.foldl_cons, List.foldl_map]

/-! ### foldr -/

theorem foldr_eq_foldr_list (f : Fin n → α → α) (x) : foldr n f x = (list n).foldr f x := by
  induction n with
  | zero => rw [foldr_zero, list_zero, List.foldr_nil]
  | succ n ih => rw [foldr_succ, ih, list_succ, List.foldr_cons, List.foldr_map]

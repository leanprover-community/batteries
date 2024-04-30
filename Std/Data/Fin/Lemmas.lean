/-
Copyright (c) 2022 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Std.Data.Fin.Basic
import Std.Data.List.Init.Lemmas
import Std.Data.Array.Init.Lemmas

namespace Fin

attribute [norm_cast] val_last

protected theorem le_antisymm_iff {x y : Fin n} : x = y ↔ x ≤ y ∧ y ≤ x :=
  Fin.ext_iff.trans Nat.le_antisymm_iff

protected theorem le_antisymm {x y : Fin n} (h1 : x ≤ y) (h2 : y ≤ x) : x = y :=
  Fin.le_antisymm_iff.2 ⟨h1, h2⟩

/-! ### clamp -/

@[simp] theorem coe_clamp (n m : Nat) : (clamp n m : Nat) = min n m := rfl

/-! ### enum/list -/

@[simp] theorem size_enum (n) : (enum n).size = n := Array.size_ofFn ..

@[simp] theorem getElem_enum (i) (h : i < (enum n).size) : (enum n)[i] = ⟨i, size_enum n ▸ h⟩ :=
  Array.getElem_ofFn ..

@[simp] theorem length_list (n) : (list n).length = n := by simp [list]

@[simp] theorem get_list (i : Fin (list n).length) : (list n).get i = i.cast (length_list n) := by
  cases i; simp only [list]; rw [← Array.getElem_eq_data_get, getElem_enum, cast_mk]

@[simp] theorem list_zero : list 0 = [] := rfl

theorem list_succ (n) : list (n+1) = 0 :: (list n).map Fin.succ := by
  apply List.ext_get; simp; intro i; cases i <;> simp

/-! ### foldl -/

theorem foldl_loop_lt (f : α → Fin n → α) (x) (h : m < n) :
    foldl.loop n f x m = foldl.loop n f (f x ⟨m, h⟩) (m+1) := by
  rw [foldl.loop, dif_pos h]

theorem foldl_loop_eq (f : α → Fin n → α) (x) : foldl.loop n f x n = x := by
  rw [foldl.loop, dif_neg (Nat.lt_irrefl _)]

theorem foldl_loop (f : α → Fin (n+1) → α) (x) (h : m < n+1) :
    foldl.loop (n+1) f x m = foldl.loop n (fun x i => f x i.succ) (f x ⟨m, h⟩) m := by
  if h' : m < n then
    rw [foldl_loop_lt _ _ h, foldl_loop_lt _ _ h', foldl_loop]; rfl
  else
    cases Nat.le_antisymm (Nat.le_of_lt_succ h) (Nat.not_lt.1 h')
    rw [foldl_loop_lt, foldl_loop_eq, foldl_loop_eq]
termination_by n - m

theorem foldl_zero (f : α → Fin 0 → α) (x) : foldl 0 f x = x := rfl

theorem foldl_succ (f : α → Fin (n+1) → α) (x) :
    foldl (n+1) f x = foldl n (fun x i => f x i.succ) (f x 0) := foldl_loop ..

theorem foldl_eq_foldl_list (f : α → Fin n → α) (x) : foldl n f x = (list n).foldl f x := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih => rw [foldl_succ, ih, list_succ, List.foldl_cons, List.foldl_map]

/-! ### foldr -/

theorem foldr_loop_zero (f : Fin n → α → α) (x) : foldr.loop n f ⟨0, Nat.zero_le _⟩ x = x := rfl

theorem foldr_loop_succ (f : Fin n → α → α) (x) (h : m < n) :
    foldr.loop n f ⟨m+1, h⟩ x = foldr.loop n f ⟨m, Nat.le_of_lt h⟩ (f ⟨m, h⟩ x) := rfl

theorem foldr_loop (f : Fin (n+1) → α → α) (x) (h : m+1 ≤ n+1) :
    foldr.loop (n+1) f ⟨m+1, h⟩ x =
      f 0 (foldr.loop n (fun i => f i.succ) ⟨m, Nat.le_of_succ_le_succ h⟩ x) := by
  induction m generalizing x with
  | zero => simp [foldr_loop_zero, foldr_loop_succ]
  | succ m ih => rw [foldr_loop_succ, ih]; rfl

theorem foldr_succ (f : Fin (n+1) → α → α) (x) :
    foldr (n+1) f x = f 0 (foldr n (fun i => f i.succ) x) := foldr_loop ..

theorem foldr_eq_foldr_list (f : Fin n → α → α) (x) : foldr n f x = (list n).foldr f x := by
  induction n with
  | zero => rfl
  | succ n ih => rw [foldr_succ, ih, list_succ, List.foldr_cons, List.foldr_map]

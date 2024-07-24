/-
Copyright (c) 2022 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Batteries.Data.Fin.Basic

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

@[simp] theorem enum_zero : (enum 0) = #[] := by simp [enum, Array.ofFn, Array.ofFn.go]

@[simp] theorem getElem_enum (i) (h : i < (enum n).size) : (enum n)[i] = ⟨i, size_enum n ▸ h⟩ :=
  Array.getElem_ofFn ..

@[simp] theorem length_list (n) : (list n).length = n := by simp [list]

@[simp] theorem getElem_list (i : Nat) (h : i < (list n).length) :
    (list n)[i] = cast (length_list n) ⟨i, h⟩ := by
  simp only [list]; rw [← Array.getElem_eq_data_getElem, getElem_enum, cast_mk]

@[deprecated getElem_list (since := "2024-06-12")]
theorem get_list (i : Fin (list n).length) : (list n).get i = i.cast (length_list n) := by
  simp [getElem_list]

@[simp] theorem list_zero : list 0 = [] := by simp [list]

theorem list_succ (n) : list (n+1) = 0 :: (list n).map Fin.succ := by
  apply List.ext_get; simp; intro i; cases i <;> simp

theorem list_succ_last (n) : list (n+1) = (list n).map castSucc ++ [last n] := by
  rw [list_succ]
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [list_succ, List.map_cons castSucc, ih]
    simp [Function.comp_def, succ_castSucc]

theorem list_reverse (n) : (list n).reverse = (list n).map rev := by
  induction n with
  | zero => rfl
  | succ n ih =>
    conv => lhs; rw [list_succ_last]
    conv => rhs; rw [list_succ]
    simp [← List.map_reverse, ih, Function.comp_def, rev_succ]

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

@[simp] theorem foldl_zero (f : α → Fin 0 → α) (x) : foldl 0 f x = x := by simp [foldl, foldl.loop]

theorem foldl_succ (f : α → Fin (n+1) → α) (x) :
    foldl (n+1) f x = foldl n (fun x i => f x i.succ) (f x 0) := foldl_loop ..

theorem foldl_succ_last (f : α → Fin (n+1) → α) (x) :
    foldl (n+1) f x = f (foldl n (f · ·.castSucc) x) (last n) := by
  rw [foldl_succ]
  induction n generalizing x with
  | zero => simp [foldl_succ, Fin.last]
  | succ n ih => rw [foldl_succ, ih (f · ·.succ), foldl_succ]; simp [succ_castSucc]

theorem foldl_eq_foldl_list (f : α → Fin n → α) (x) : foldl n f x = (list n).foldl f x := by
  induction n generalizing x with
  | zero => rw [foldl_zero, list_zero, List.foldl_nil]
  | succ n ih => rw [foldl_succ, ih, list_succ, List.foldl_cons, List.foldl_map]

/-! ### foldr -/

unseal foldr.loop in
theorem foldr_loop_zero (f : Fin n → α → α) (x) : foldr.loop n f ⟨0, Nat.zero_le _⟩ x = x :=
  rfl

unseal foldr.loop in
theorem foldr_loop_succ (f : Fin n → α → α) (x) (h : m < n) :
    foldr.loop n f ⟨m+1, h⟩ x = foldr.loop n f ⟨m, Nat.le_of_lt h⟩ (f ⟨m, h⟩ x) :=
  rfl

theorem foldr_loop (f : Fin (n+1) → α → α) (x) (h : m+1 ≤ n+1) :
    foldr.loop (n+1) f ⟨m+1, h⟩ x =
      f 0 (foldr.loop n (fun i => f i.succ) ⟨m, Nat.le_of_succ_le_succ h⟩ x) := by
  induction m generalizing x with
  | zero => simp [foldr_loop_zero, foldr_loop_succ]
  | succ m ih => rw [foldr_loop_succ, ih, foldr_loop_succ, Fin.succ]

@[simp] theorem foldr_zero (f : Fin 0 → α → α) (x) :
    foldr 0 f x = x := foldr_loop_zero ..

theorem foldr_succ (f : Fin (n+1) → α → α) (x) :
    foldr (n+1) f x = f 0 (foldr n (fun i => f i.succ) x) := foldr_loop ..

theorem foldr_succ_last (f : Fin (n+1) → α → α) (x) :
    foldr (n+1) f x = foldr n (f ·.castSucc) (f (last n) x) := by
  induction n generalizing x with
  | zero => simp [foldr_succ, Fin.last]
  | succ n ih => rw [foldr_succ, ih (f ·.succ), foldr_succ]; simp [succ_castSucc]

theorem foldr_eq_foldr_list (f : Fin n → α → α) (x) : foldr n f x = (list n).foldr f x := by
  induction n with
  | zero => rw [foldr_zero, list_zero, List.foldr_nil]
  | succ n ih => rw [foldr_succ, ih, list_succ, List.foldr_cons, List.foldr_map]

/-! ### foldl/foldr -/

theorem foldl_rev (f : Fin n → α → α) (x) :
    foldl n (fun x i => f i.rev x) x = foldr n f x := by
  induction n generalizing x with
  | zero => simp
  | succ n ih => rw [foldl_succ, foldr_succ_last, ← ih]; simp [rev_succ]

theorem foldr_rev (f : α → Fin n → α) (x) :
     foldr n (fun i x => f x i.rev) x = foldl n f x := by
  induction n generalizing x with
  | zero => simp
  | succ n ih => rw [foldl_succ_last, foldr_succ, ← ih]; simp [rev_succ]

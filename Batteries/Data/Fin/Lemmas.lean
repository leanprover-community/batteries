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

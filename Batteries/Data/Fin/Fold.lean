/-
Copyright (c) 2024 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: François G. Dorais
-/
import Batteries.Data.List.FinRange

namespace Fin

theorem foldlM_eq_foldlM_finRange [Monad m] (f : α → Fin n → m α) (x) :
    foldlM n f x = (List.finRange n).foldlM f x := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    rw [foldlM_succ, List.finRange_succ, List.foldlM_cons]
    congr; funext
    rw [List.foldlM_map, ih]

@[deprecated (since := "2024-11-19")]
alias foldlM_eq_foldlM_list := foldlM_eq_foldlM_finRange

theorem foldrM_eq_foldrM_finRange [Monad m] [LawfulMonad m] (f : Fin n → α → m α) (x) :
    foldrM n f x = (List.finRange n).foldrM f x := by
  induction n with
  | zero => simp
  | succ n ih => rw [foldrM_succ, ih, List.finRange_succ, List.foldrM_cons, List.foldrM_map]

@[deprecated (since := "2024-11-19")]
alias foldrM_eq_foldrM_list := foldrM_eq_foldrM_finRange

theorem foldl_eq_foldl_finRange (f : α → Fin n → α) (x) :
    foldl n f x = (List.finRange n).foldl f x := by
  induction n generalizing x with
  | zero => rw [foldl_zero, List.finRange_zero, List.foldl_nil]
  | succ n ih => rw [foldl_succ, ih, List.finRange_succ, List.foldl_cons, List.foldl_map]

@[deprecated (since := "2024-11-19")]
alias foldl_eq_foldl_list := foldl_eq_foldl_finRange

theorem foldr_eq_foldr_finRange (f : Fin n → α → α) (x) :
    foldr n f x = (List.finRange n).foldr f x := by
  induction n with
  | zero => rw [foldr_zero, List.finRange_zero, List.foldr_nil]
  | succ n ih => rw [foldr_succ, ih, List.finRange_succ, List.foldr_cons, List.foldr_map]

@[deprecated (since := "2024-11-19")]
alias foldr_eq_foldr_list := foldr_eq_foldr_finRange

variable (n : Nat) (α : Fin (n + 1) → Sort _)

/-- Dependent version of `Fin.foldl`. -/
def fold (f : ∀ (i : Fin n), α i.castSucc → α i.succ) (init : α 0) : α (last n) :=
    loop 0 (Nat.zero_lt_succ n) init where
  loop (i : Nat) (h : i < n + 1) (x : α ⟨i, h⟩) : α (last n) :=
    if h' : i < n then
      loop (i + 1) (Nat.succ_lt_succ h') (f ⟨i, h'⟩ x)
    else
      haveI : ⟨i, h⟩ = last n := by
        ext
        simp only [val_last]
        exact Nat.eq_of_lt_succ_of_not_lt h h'
      _root_.cast (congrArg α this) x
  termination_by n - i
  decreasing_by
    exact Nat.sub_add_lt_sub h' (Nat.lt_add_one 0)

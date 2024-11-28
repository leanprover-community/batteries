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

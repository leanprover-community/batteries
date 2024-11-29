/-
Copyright (c) 2024 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: François G. Dorais
-/
import Batteries.Data.List.OfFn

namespace List

@[simp] theorem length_finRange (n) : (List.finRange n).length = n := by
  simp [List.finRange]

@[deprecated (since := "2024-11-19")]
alias length_list := length_finRange

@[simp] theorem getElem_finRange (i : Nat) (h : i < (List.finRange n).length) :
    (finRange n)[i] = Fin.cast (length_finRange n) ⟨i, h⟩ := by
  simp [List.finRange]

@[deprecated (since := "2024-11-19")]
alias getElem_list := getElem_finRange

@[simp] theorem finRange_zero : finRange 0 = [] := by simp [finRange, ofFn]

@[deprecated (since := "2024-11-19")]
alias list_zero := finRange_zero

theorem finRange_succ (n) : finRange (n+1) = 0 :: (finRange n).map Fin.succ := by
  apply List.ext_getElem; simp; intro i; cases i <;> simp

@[deprecated (since := "2024-11-19")]
alias list_succ := finRange_succ

theorem finRange_succ_last (n) :
    finRange (n+1) = (finRange n).map Fin.castSucc ++ [Fin.last n] := by
  apply List.ext_getElem
  · simp
  · intros
    simp only [List.finRange, List.getElem_ofFn, getElem_append, length_map, length_ofFn,
      getElem_map, Fin.castSucc_mk, getElem_singleton]
    split
    · rfl
    · next h => exact Fin.eq_last_of_not_lt h

@[deprecated (since := "2024-11-19")]
alias list_succ_last := finRange_succ_last

theorem finRange_reverse (n) : (finRange n).reverse = (finRange n).map Fin.rev := by
  induction n with
  | zero => simp
  | succ n ih =>
    conv => lhs; rw [finRange_succ_last]
    conv => rhs; rw [finRange_succ]
    rw [reverse_append, reverse_cons, reverse_nil, nil_append, singleton_append, ← map_reverse,
      map_cons, ih, map_map, map_map]
    congr; funext
    simp [Fin.rev_succ]

@[deprecated (since := "2024-11-19")]
alias list_reverse := finRange_reverse

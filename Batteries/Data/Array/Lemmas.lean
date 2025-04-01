/-
Copyright (c) 2021 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Mario Carneiro, Gabriel Ebner
-/
import Batteries.Data.List.Lemmas
import Batteries.Data.List.FinRange
import Batteries.Data.Array.Basic
import Batteries.Tactic.SeqFocus
import Batteries.Util.ProofWanted

namespace Array

theorem forIn_eq_forIn_toList [Monad m]
    (as : Array α) (b : β) (f : α → β → m (ForInStep β)) :
    forIn as b f = forIn as.toList b f := by
  cases as
  simp

@[deprecated (since := "2024-09-09")] alias forIn_eq_forIn_data := forIn_eq_forIn_toList

/-! ### zipWith / zip -/

@[deprecated (since := "2024-09-09")] alias data_zipWith := toList_zipWith

/-! ### flatten -/

@[deprecated (since := "2024-09-09")] alias data_join := toList_flatten
@[deprecated (since := "2024-10-15")] alias mem_join := mem_flatten

/-! ### indexOf? -/

open List

theorem idxOf?_toList [BEq α] {a : α} {l : Array α} :
    l.toList.idxOf? a = l.idxOf? a := by
  rcases l with ⟨l⟩
  simp

/-! ### erase -/

@[deprecated (since := "2025-02-06")] alias eraseP_toArray := List.eraseP_toArray
@[deprecated (since := "2025-02-06")] alias erase_toArray := List.erase_toArray

@[simp] theorem toList_erase [BEq α] (l : Array α) (a : α) :
    (l.erase a).toList = l.toList.erase a := by
  rcases l with ⟨l⟩
  simp

@[simp] theorem size_eraseIdxIfInBounds (a : Array α) (i : Nat) :
    (a.eraseIdxIfInBounds i).size = if i < a.size then a.size-1 else a.size := by
  simp only [eraseIdxIfInBounds]; split; simp; rfl

/-! ### set -/

theorem size_set! (a : Array α) (i v) : (a.set! i v).size = a.size := by simp

/-! ### map -/

/-! ### mem -/

/-! ### insertAt -/

@[deprecated (since := "2024-11-20")] alias size_insertAt := size_insertIdx
@[deprecated (since := "2024-11-20")] alias getElem_insertAt_lt := getElem_insertIdx_of_lt
@[deprecated (since := "2024-11-20")] alias getElem_insertAt_eq := getElem_insertIdx_self
@[deprecated (since := "2024-11-20")] alias getElem_insertAt_gt := getElem_insertIdx_of_gt

@[deprecated (since := "2025-02-06")] alias getElem_insertIdx_lt := getElem_insertIdx_of_lt
@[deprecated (since := "2025-02-06")] alias getElem_insertIdx_eq := getElem_insertIdx_self
@[deprecated (since := "2025-02-06")] alias getElem_insertIdx_gt := getElem_insertIdx_of_gt

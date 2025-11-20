/-
Copyright (c) 2021 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Mario Carneiro, Gabriel Ebner
-/
module

public import Batteries.Data.List.Lemmas

@[expose] public section

namespace Array

@[deprecated forIn_toList (since := "2025-07-01")]
theorem forIn_eq_forIn_toList [Monad m]
    (as : Array α) (b : β) (f : α → β → m (ForInStep β)) :
    forIn as b f = forIn as.toList b f := by
  cases as
  simp

/-! ### idxOf? -/

open List

@[grind =]
theorem idxOf?_toList [BEq α] {a : α} {l : Array α} :
    l.toList.idxOf? a = l.idxOf? a := by
  rcases l with ⟨l⟩
  simp

/-! ### erase -/

@[deprecated (since := "2025-02-06")] alias eraseP_toArray := List.eraseP_toArray
@[deprecated (since := "2025-02-06")] alias erase_toArray := List.erase_toArray

@[simp, grind =] theorem toList_erase [BEq α] (l : Array α) (a : α) :
    (l.erase a).toList = l.toList.erase a := by
  rcases l with ⟨l⟩
  simp

@[simp] theorem size_eraseIdxIfInBounds (a : Array α) (i : Nat) :
    (a.eraseIdxIfInBounds i).size = if i < a.size then a.size-1 else a.size := by
  grind

/-! ### set -/

theorem size_set! (a : Array α) (i v) : (a.set! i v).size = a.size := by simp

/-! ### map -/

/-! ### mem -/

/-! ### insertAt -/

@[deprecated (since := "2025-02-06")] alias getElem_insertIdx_lt := getElem_insertIdx_of_lt
@[deprecated (since := "2025-02-06")] alias getElem_insertIdx_eq := getElem_insertIdx_self
@[deprecated (since := "2025-02-06")] alias getElem_insertIdx_gt := getElem_insertIdx_of_gt

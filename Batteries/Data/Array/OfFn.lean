/-
Copyright (c) 2024 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Batteries.Data.List.OfFn

open List

namespace Array

/-! ### ofFn -/

@[simp]
theorem toList_ofFn (f : Fin n → α) : (ofFn f).toList = List.ofFn f := by
  ext1
  rw [List.getElem?_eq]
  simp [ofFnNthVal]
  split
  · rw [← getElem_eq_data_getElem]
    simp
  · rfl

end Array

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
theorem data_ofFn (f : Fin n → α) : (ofFn f).data = List.ofFn f := by
  ext1
  simp only [getElem?_eq, data_length, size_ofFn, length_ofFn, getElem_ofFn]
  split
  · rw [← getElem_eq_data_getElem]
    simp
  · rfl

end Array

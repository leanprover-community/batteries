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
  apply ext_getElem <;> simp

end Array

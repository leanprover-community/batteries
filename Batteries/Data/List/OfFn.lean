/-
Copyright (c) 2024 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Batteries.Data.List.Lemmas

/-!
# Theorems about `List.ofFn`
-/

namespace List

@[simp]
theorem length_ofFn_go {n} (f : Fin n → α) (i j h) : length (ofFn.go f i j h) = i := by
  induction i generalizing j <;> simp_all [ofFn.go]

/-- The length of a list converted from a function is the size of the domain. -/
@[simp]
theorem length_ofFn {n} (f : Fin n → α) : length (ofFn f) = n := by
  simp [ofFn, length_ofFn_go]

theorem getElem_ofFn_go {n} (f : Fin n → α) (i j h) (k) (hk : k < (ofFn.go f i j h).length) :
    (ofFn.go f i j h)[k] = f ⟨j + k, by simp at hk; omega⟩ := by
  let i+1 := i
  cases k <;> simp [ofFn.go, getElem_ofFn_go (i := i)]
  congr 2; omega

@[simp]
theorem getElem_ofFn {n} (f : Fin n → α) (i : Nat) (h : i < (ofFn f).length) :
    (ofFn f)[i] = f ⟨i, by simp_all⟩ := by
  simp [ofFn, getElem_ofFn_go]

/-- The `n`th element of a list -/
@[simp]
theorem getElem?_ofFn {n} (f : Fin n → α) (i) : (ofFn f)[i]? = ofFnNthVal f i :=
  if h : i < (ofFn f).length
  then by
    rw [getElem?_eq_getElem h, getElem_ofFn]
    · simp only [length_ofFn] at h; simp [ofFnNthVal, h]
  else by
    rw [ofFnNthVal, dif_neg] <;>
    simpa using h

@[simp] theorem ofFn_toArray (f : Fin n → α) : (ofFn f).toArray = Array.ofFn f := by
  ext <;> simp

end List

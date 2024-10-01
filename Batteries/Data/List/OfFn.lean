/-
Copyright (c) 2024 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Batteries.Data.List.Lemmas
import Batteries.Data.Fin.Lemmas

/-!
# Theorems about `List.ofFn`
-/

namespace List

@[simp]
theorem length_ofFn (f : Fin n → α) : (ofFn f).length = n := by
  simp only [ofFn]
  induction n with
  | zero => simp
  | succ n ih => simp [Fin.foldr_succ, ih]

@[simp]
protected theorem getElem_ofFn (f : Fin n → α) (i : Nat) (h : i < (ofFn f).length) :
    (ofFn f)[i] = f ⟨i, by simp_all⟩ := by
  simp only [ofFn]
  induction n generalizing i with
  | zero => simp at h
  | succ n ih =>
    match i with
    | 0 => simp [Fin.foldr_succ]
    | i+1 =>
      simp only [Fin.foldr_succ]
      apply ih
      simp_all

@[simp]
protected theorem getElem?_ofFn (f : Fin n → α) (i) : (ofFn f)[i]? = ofFnNthVal f i :=
  if h : i < (ofFn f).length
  then by
    rw [getElem?_eq_getElem h, List.getElem_ofFn]
    · simp only [length_ofFn] at h; simp [ofFnNthVal, h]
  else by
    rw [ofFnNthVal, dif_neg] <;>
    simpa using h

@[simp] theorem toArray_ofFn (f : Fin n → α) : (ofFn f).toArray = Array.ofFn f := by
  ext <;> simp

end List

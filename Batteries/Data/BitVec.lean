/-
Copyright (c) 2024 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: François G. Dorais
-/

namespace BitVec

theorem getElem_shifConcat (v : BitVec n) (b : Bool) (i) (h : i < n) :
    (v.shiftConcat b)[i] = if i = 0 then b else v[i-1] := by
  rw [← getLsbD_eq_getElem, getLsbD_shiftConcat, getLsbD_eq_getElem, decide_eq_true h,
    Bool.true_and]

@[simp] theorem getElem_shiftConcat_zero (v : BitVec n) (b : Bool) (h : 0 < n) :
    (v.shiftConcat b)[0] = b := by simp [getElem_shifConcat]

@[simp] theorem getElem_shiftConcat_succ (v : BitVec n) (b : Bool) (h : i + 1 < n) :
    (v.shiftConcat b)[i+1] = v[i] := by simp [getElem_shifConcat]

/-- `ofFnAux f` returns the `BitVec m` whose `i`th bit is `f i` when `i < m` -/
@[inline] def ofFnAux (m : Nat) (f : Fin n → Bool) : BitVec m :=
  Fin.foldr n (fun i v => v.shiftConcat (f i)) 0

/-- `ofFn f` returns the `BitVec n` whose `i`th bit is `f i` -/
abbrev ofFn (f : Fin n → Bool) : BitVec n := ofFnAux n f

theorem getElem_ofFnAux (f : Fin n → Bool) (i) (h : i < n) (h' : i < m) :
    (ofFnAux m f)[i] = f ⟨i, h⟩ := by
  simp only [ofFnAux]
  induction n generalizing i m with
  | zero => contradiction
  | succ n ih =>
    simp only [Fin.foldr_succ, getElem_shifConcat]
    cases i with
    | zero =>
      simp
    | succ i =>
      rw [ih (fun i => f i.succ)] <;> try omega
      simp

@[simp] theorem getElem_ofFn (f : Fin n → Bool) (i) (h : i < n) : (ofFn f)[i] = f ⟨i, h⟩ :=
  getElem_ofFnAux ..

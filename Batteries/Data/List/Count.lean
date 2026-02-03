/-
Copyright (c) 2014 Parikshit Khanna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Parikshit Khanna, Jeremy Avigad, Leonardo de Moura, Floris van Doorn, Mario Carneiro
-/
module
public import Batteries.Data.List.Lemmas

@[expose] public section

/-!
# Counting in lists

This file proves basic properties of `List.countP` and `List.count`, which count the number of
elements of a list satisfying a predicate and equal to a given element respectively. Their
definitions can be found in `Batteries.Data.List.Basic`.
-/


open Nat

namespace List

/-! ### count -/

section count

theorem count_singleton' [DecidableEq α] (a b : α) : count a [b] = if b = a then 1 else 0 :=
  count_singleton.trans (by grind)

theorem count_concat [BEq α] [LawfulBEq α] (a : α) (l : List α) :
    count a (concat l a) = count a l + 1 := by simp

/-! ### idxToSigmaCount, sigmaCountToIdx -/

/-- `idxToSigmaCount` is essentially a `Fin`-to-`Fin` wrapper for `countBefore` that also
includes the corresponding element. For example:
```
idxToSigmaCount [5, 1, 3, 2, 4, 0, 1, 4] 5 = ⟨0, 0⟩
```
-/
def idxToSigmaCount [BEq α] [ReflBEq α] (xs : List α) (i : Fin (xs.length)) :
    (x : α) × Fin (xs.count x) :=
  ⟨xs[i.1], xs.countBefore xs[i.1] i, countBefore_lt_count_of_lt_length_of_beq _ BEq.rfl⟩

@[simp, grind =]
theorem fst_idxToSigmaCount [BEq α] [ReflBEq α] {xs: List α} {i : Fin (xs.length)} :
    (xs.idxToSigmaCount i).1 = xs[i.1] := rfl

@[simp, grind =]
theorem snd_idxToSigmaCount [BEq α] [ReflBEq α] {xs: List α} {i : Fin (xs.length)} :
    (xs.idxToSigmaCount i).2 =
    ⟨xs.countBefore xs[i.1] i, countBefore_lt_count_of_lt_length_of_beq _ BEq.rfl⟩ := rfl

@[simp, grind =]
theorem coe_snd_idxToSigmaCount [BEq α] [ReflBEq α] {xs: List α} {i : Fin (xs.length)} :
    ((xs.idxToSigmaCount i).2 : Nat) = xs.countBefore xs[i.1] i := rfl

/-- `sigmaCountToIdx` is a `_ × Fin`-to-`Fin` wrapper for `countBefore`.
For example:
```
sigmaCountToIdx [5, 1, 3, 2, 4, 0, 1, 4] ⟨0, 0⟩ = 5
```
-/
def sigmaCountToIdx [BEq α] (xs : List α) (xc : (x : α) × Fin (xs.count x)) :
    Fin (xs.length) := ⟨xs.idxOfNth xc.1 xc.2, idxOfNth_lt_length_of_lt_count xc.2.isLt⟩

@[simp, grind =]
theorem coe_sigmaCountToIdx [BEq α] {xs: List α} {xc : (x : α) × Fin (xs.count x)} :
    (xs.sigmaCountToIdx xc : Nat) = xs.idxOfNth xc.1 xc.2 := rfl

@[simp, grind =]
theorem sigmaCountToIdx_idxToSigmaCount [BEq α] [ReflBEq α] {xs : List α}
    {i : Fin (xs.length)} : xs.sigmaCountToIdx (xs.idxToSigmaCount i) = i :=
  Fin.ext <| idxOfNth_countBefore_of_lt_length_of_beq _ BEq.rfl

@[simp, grind =]
theorem idxToSigmaCount_sigmaCountToIdx [BEq α] [LawfulBEq α] {xs : List α}
    {xc : (x : α) × Fin (xs.count x)} : xs.idxToSigmaCount (xs.sigmaCountToIdx xc) = xc :=
  Sigma.ext getElem_idxOfNth_eq (heq_of_eqRec_eq (by simp) (by grind))

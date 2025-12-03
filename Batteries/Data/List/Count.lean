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
    count a (concat l a) = succ (count a l) := by simp

/-! ### countToIdx, idxToCount -/

/-- `idxToCount` is a `Fin`-to-`Fin` wrapper for `countBefore`. -/
def idxToCount [BEq α] [ReflBEq α] {xs: List α} (i : Fin (xs.length)) :
    Fin (xs.count xs[i.1]) :=
  ⟨xs.countBefore xs[i.1] i, countBefore_lt_count_of_lt_length_of_beq _ BEq.rfl⟩

@[simp, grind =]
theorem coe_idxToCount [BEq α] [ReflBEq α] {xs: List α} {i : Fin (xs.length)} :
    (xs.idxToCount i : Nat) = xs.countBefore xs[i.1] i := rfl

/-- `countToIdx` is a `_ × Fin`-to-`Fin` wrapper for `countBefore`. -/
def countToIdx [BEq α] {xs: List α} (x : α) (i : Fin (xs.count x)) :
    Fin (xs.length) := ⟨xs.idxOfNth x i, idxOfNth_lt_length_of_lt_count i.isLt⟩

@[simp, grind =]
theorem coe_countToIdx [BEq α] {xs: List α} {x : α} {i : Fin (xs.count x)} :
    (xs.countToIdx x i : Nat) = xs.idxOfNth x i := rfl

@[simp, grind =]
theorem countToIdx_getElem_idxToCount [BEq α] [ReflBEq α] {xs: List α} {i : Fin (xs.length)} :
    xs.countToIdx xs[i.1] (xs.idxToCount i) = i :=
  Fin.ext <| idxOfNth_countBefore_of_lt_length_of_beq _ BEq.rfl

theorem getElem_countToIdx_beq [BEq α] {xs: List α} {x : α} {i : Fin (xs.count x)} :
    xs[(xs.countToIdx x i : Nat)] == x := getElem_idxOfNth_beq

theorem getElem_countToIdx_eq [BEq α] [LawfulBEq α] {xs: List α} {x : α} {i : Fin (xs.count x)} :
    xs[(xs.countToIdx x i : Nat)] = x := by simp

@[simp, grind =]
theorem coe_idxToCount_countToIdx [BEq α] [LawfulBEq α] {xs: List α} {x : α}
    {i : Fin (xs.count x)} : (xs.idxToCount (xs.countToIdx x i) : Nat) = i := by
  simp [countBefore_idxOfNth_of_lt_count]

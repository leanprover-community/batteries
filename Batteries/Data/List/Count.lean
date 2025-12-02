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

variable [BEq α]

theorem count_concat [LawfulBEq α] (a : α) (l : List α) :
    count a (concat l a) = succ (count a l) := by simp



/-- For a fixed list, given the index of an element,
  find the corresponding element and multiplicity. -/
def idxToCountElem [EquivBEq α] (xs : List α) (i : Fin xs.length) :
    (x : α) × Fin (xs.count x) := ⟨xs[i], (xs.idxsOf xs[i]).idxOf i.val, by grind⟩

@[simp, grind =]
theorem fst_idxToCountElem [EquivBEq α] (xs : List α) (i : Fin xs.length) :
  (xs.idxToCountElem i).fst = xs[(i : Nat)] := rfl

@[simp, grind =]
theorem val_snd_idxToCountElem [EquivBEq α] (xs : List α) (i : Fin xs.length) :
  (xs.idxToCountElem i).snd = (xs.idxsOf xs[(i : Nat)]).idxOf i.1 := rfl

/-- For a fixed list, given an element and its multiplicity,
  find the corresponding index. -/
def countElemToIdx (xs : List α) (xj : (x : α) × Fin (xs.count x)) : Fin xs.length :=
  ⟨(xs.idxsOf xj.1)[xj.2.1], xs.getElem_idxsOf_lt_add _⟩

@[simp, grind =]
theorem val_countElemToIdx (xs : List α) (xj : (x : α) × Fin (xs.count x)) :
  xs.countElemToIdx xj = (xs.idxsOf xj.1)[xj.2.1] := rfl

theorem countElemToIdx_idxToCountElem {xs : List α} [LawfulBEq α]
    (xj : (x : α) × Fin (xs.count x)) :
    xs.idxToCountElem (xs.countElemToIdx xj) = xj := by
  have H {k l} : k = l → {i : Fin k} → {j : Fin l} → (i : Nat) = j → i ≍ j := by grind [Fin.ext_iff]
  simp [H, Sigma.ext_iff]

theorem idxToCountElem_countElemToIdx {xs : List α} [LawfulBEq α]
    (i : Fin xs.length) :
    xs.countElemToIdx (xs.idxToCountElem i) = i := Fin.ext <| by simp

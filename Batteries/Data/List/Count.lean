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



/-- For a fixed list, given the index of an element,
  find the corresponding element and multiplicity. -/
def idxToCountElem [EquivBEq α] (xs : List α) (i : Fin xs.length) :
    (x : α) × Fin (xs.count x) := ⟨xs[i], (xs.idxsOf xs[i]).idxOf i.val, by grind⟩

/-- For a fixed list, given the index of an element, count the number of times that element appears
    prior to that element.

    For example:
    * `idxToCount ['a', 'b', 'b', 'c', 'a', 'd', 'b'] 0 (by decide) = 0`
    * `idxToCount ['a', 'b', 'b', 'c', 'a', 'd', 'b'] 2 (by decide) = 1`
    * `idxToCount ['a', 'b', 'b', 'c', 'a', 'd', 'b'] 5 (by decide) = 0`
    * `idxToCount ['a', 'b', 'b', 'c', 'a', 'd', 'b'] 6 (by decide) = 2`

-/
def idxToCount [BEq α] (xs : List α) (i : Nat) (hi : i < xs.length) : Nat := go xs i hi 0 where
  @[specialize] go : (xs : List α) → (i : Nat) → i < xs.length → Nat → Nat
  | _ :: _, 0, _, acc => acc
  | x :: xs, i + 1, hi, acc =>
    haveI hi := Nat.lt_of_succ_lt_succ hi
    bif x == xs[i] then go xs i hi (acc + 1) else go xs i hi acc

def idxToCount' [BEq α] : (xs : List α) → (i : Nat) → (start : Nat := 0) → Nat
  | [], _, acc => acc
  | _ :: _, 0, acc => acc
  | x :: xs, i + 1, acc => idxToCount' xs i (acc + (x == xs[i]?.getD x).toNat)

/-! ### idxToCount -/

protected theorem idxToCount_go_eq_add [BEq α] :
    idxToCount.go (xs : List α) i hi n = idxToCount.go (xs : List α) i hi 0 + n := by
  induction xs generalizing i n
  · grind
  · unfold idxToCount.go; cases i <;> grind

@[grind =]
theorem idxToCount'_eq_count_getElem_take_add_of_lt [BEq α] (hi : i < xs.length) :
    idxToCount' (xs : List α) i s = (xs.take i).count xs[i] + s := by
  induction xs generalizing i s <;> unfold idxToCount' <;> grind

@[grind =]
theorem idxToCount'_eq_count_getElem_take_add_of_ge [BEq α] [EquivBEq α ] (hi : xs.length ≤ i) :
    idxToCount' (xs : List α) i s = xs.length + s := by
  induction xs generalizing i s <;> unfold idxToCount'
  · grind
  · cases i
    · grind
    · simp
      rw [List.getElem?_eq_none (by grind)]
      rw [Option.getD_none]
      grind

theorem idxToCount'_go_eq_add [BEq α] :
    idxToCount' (xs : List α) i n = idxToCount' (xs : List α) i 0 + n := by
  induction xs generalizing i n <;> unfold idxToCount' <;> grind


@[grind =]
theorem idxToCount_eq_count_getElem_take [BEq α] :
    idxToCount (xs : List α) i hi = (xs.take i).count xs[i] := by
  unfold idxToCount
  induction xs generalizing i with
  | nil => grind | cons =>
    cases i
    · rfl
    · unfold idxToCount.go; grind [List.idxToCount_go_eq_add]

theorem idxToCount_zero [BEq α] : {xs : List α} → {hi : 0 < xs.length} →
    idxToCount xs 0 hi = 0 := by grind

theorem idxToCount_succ_cons [BEq α] {xs : List α} {i : Nat} {hi : i + 1 < (x :: xs).length} :
    idxToCount (x :: xs) (i + 1) hi = if x == xs[i]'(by grind)
    then idxToCount xs i (by grind) + 1 else idxToCount xs i (by grind) := by grind

theorem idxToCount_succ_cons_of_pos [BEq α] {xs : List α} {i : Nat} {hi : i + 1 < (x :: xs).length}
  (h : x == xs[i]'(by grind)) :
    idxToCount (x :: xs) (i + 1) hi = idxToCount xs i (by grind) + 1 := by grind

theorem idxToCount_succ_cons_of_neg [BEq α] {xs : List α} {i : Nat} {hi : i + 1 < (x :: xs).length}
  (h : (x == xs[i]'(by grind)) = false) :
    idxToCount (x :: xs) (i + 1) hi = idxToCount xs i (by grind) := by grind

theorem idxToCount_succ [BEq α] : idxToCount (xs : List α) (i + 1) hi =
    if (xs.head <| by grind) == xs.tail[i]'(by grind) then
      idxToCount xs.tail i (by grind) + 1 else
      idxToCount xs.tail i (by grind) := by cases xs <;> grind

theorem idxToCount_lt_count_getElem [BEq α] [EquivBEq α] :
    idxToCount (xs : List α) i hi < xs.count xs[i] := by grind

theorem idxToCount_eq_idxOf_idxsOf [BEq α] [LawfulBEq α] :
    idxToCount xs i hi = ((xs : List α).idxsOf xs[i] s).idxOf (i + s) := by
  rw [idxToCount_eq_count_getElem_take]
  induction xs generalizing i s with | nil | cons x xs IH
  · grind
  · cases i <;> grind

/-! ### countToIdx -/

/-- For a fixed list, given an element and an index corresponding to an appearance of that element
    in the list, find the index of that entry in the list.

    For example:
    * `countToIdx 'a' ['a', 'b', 'b', 'c', 'a', 'd', 'b'] 0 (by decide) = 0`
    * `countToIdx 'a' ['a', 'b', 'b', 'c', 'a', 'd', 'b'] 1 (by decide) = 4`
    * `countToIdx 'b' ['a', 'b', 'b', 'c', 'a', 'd', 'b'] 1 (by decide) = 2`
    * `countToIdx 'b' ['a', 'b', 'b', 'c', 'a', 'd', 'b'] 2 (by decide) = 6`
-/
def countToIdx [BEq α] (a : α) : (xs : List α) → (i : Nat) → (hi : i < xs.count a) →
    (start : Nat := 0) → Nat
  | x :: xs, i, hi, acc =>
    match h : x == a with
    | false =>
      haveI hi := (Nat.lt_of_lt_of_eq hi (count_cons.trans <| h ▸ rfl))
      countToIdx a xs i hi (acc + 1)
    | true => match i with
      | 0 => acc
      | i + 1 =>
        haveI hi := Nat.lt_of_succ_lt_succ <| Nat.lt_of_lt_of_eq hi <|
            count_cons.trans <| h.symm ▸ rfl
        countToIdx a xs i hi (acc + 1)

protected theorem countToIdx_start [BEq α] {a xs i hi} :
    countToIdx a (xs : List α) i hi s = countToIdx a xs i hi 0 + s := by
  induction xs generalizing i s
  · grind
  · cases i <;> grind [countToIdx]

@[grind =]
theorem countToIdx_eq_getElem_idxsOf [BEq α] {a xs i hi}  :
    countToIdx a (xs : List α) i hi s = (xs.idxsOf a s)[i]'(by grind) := by
  induction xs generalizing i s with
  | nil => grind | cons x xs IH =>
    unfold countToIdx;
    split
    · grind
    · cases i <;> grind

theorem le_countToIdx [BEq α] {a xs i hi} (s := 0) :
    s ≤ countToIdx a (xs : List α) i hi s := by grind

theorem countToIdx_lt_length_add [BEq α] {a xs i hi} (s := 0) :
    countToIdx a (xs : List α) i hi s < xs.length + s := by grind

theorem countToIdx_lt_length [BEq α] {a xs i hi}  :
    countToIdx a (xs : List α) i hi < xs.length := by grind

theorem getElem_countToIdx [BEq α] {xs a i hi} :
    xs[countToIdx a (xs : List α) i hi s - s]'(by grind) == a := by
  simp [countToIdx_eq_getElem_idxsOf, getElem_getElem_idxsOf_sub]

theorem getElem_countToIdx_of_lawful [BEq α] [LawfulBEq α] {xs a i hi} :
    xs[countToIdx a (xs : List α) i hi s - s]'(by grind) = a := by grind [getElem_countToIdx]

theorem countToIdx_idxToCount [BEq α] [EquivBEq α] {xs i hi} :
    (xs : List α).countToIdx xs[i] (xs.idxToCount i hi) idxToCount_lt_count_getElem s = i + s := by
  simp only [countToIdx_eq_getElem_idxsOf, idxToCount_eq_count_getElem_take]
  induction xs generalizing i s with | nil | cons x xs IH
  · grind
  · simp only [idxsOf_cons]
    cases i with | zero | succ i
    · simp only [getElem_cons_zero, BEq.rfl, cond_true, take_zero, count_nil,
      Nat.zero_add]
    · simp only [getElem_cons_succ, take_succ_cons, count_cons]
      split <;> grind

theorem idxToCount_countToIdx [BEq α] [LawfulBEq α] {a xs i hi} :
    (xs : List α).idxToCount (xs.countToIdx a i hi s - s)
    (Nat.sub_lt_right_of_lt_add (le_countToIdx _) (countToIdx_lt_length_add _)) = i := by
  simp only [countToIdx_eq_getElem_idxsOf, idxToCount_eq_idxOf_idxsOf (s := s), le_getElem_idxsOf,
    Nat.sub_add_cancel, getElem_getElem_idxsOf_sub_of_lawful, nodup_idxsOf, Nodup.idxOf_getElem]

/-- For a fixed list, given the index of an element,
  find the corresponding element and multiplicity. -/
def idxToCountElem [BEq α] [EquivBEq α] (xs : List α) (i : Fin xs.length) :
    (x : α) × Fin (xs.count x) := ⟨xs[i], xs.idxToCount i i.is_lt, idxToCount_lt_count_getElem⟩

@[simp, grind =]
theorem fst_idxToCountElem [BEq α] [EquivBEq α] (xs : List α) (i : Fin xs.length) :
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

theorem countElemToIdx_idxToCountElem  [BEq α] [LawfulBEq α] {xs : List α}
    (xj : (x : α) × Fin (xs.count x)) :
    xs.idxToCountElem (xs.countElemToIdx xj) = xj := by
  have H {k l} : k = l → {i : Fin k} → {j : Fin l} → (i : Nat) = j → i ≍ j := by grind [Fin.ext_iff]
  rw [Sigma.ext_iff]
  simp [getElem_countToIdx]
  apply H
  simp [getElem_countToIdx]
  simp
  simp [H, Sigma.ext_iff]

theorem idxToCountElem_countElemToIdx {xs : List α} [LawfulBEq α]
    (i : Fin xs.length) :
    xs.countElemToIdx (xs.idxToCountElem i) = i := Fin.ext <| by simp

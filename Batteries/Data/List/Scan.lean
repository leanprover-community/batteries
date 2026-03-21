/-
Copyright (c) 2014 Parikshit Khanna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Parikshit Khanna, Jeremy Avigad, Leonardo de Moura, Floris van Doorn, Mario Carneiro
-/
module

public import Batteries.Data.List.Basic
public import Batteries.Data.List.Lemmas
import Batteries.Util.ProofWanted
meta import Batteries.Tactic.Init

@[expose] public section

/-!
# List scan

Prove basic results about `List.scanl`, `List.scanr`, `List.scanlM` and `List.scanrM`.
-/

namespace List

/-! ### partialSums/partialProd -/

@[simp, grind =]
theorem length_partialSums [Add α] [Zero α] {l : List α} :
    l.partialSums.length = l.length + 1 := by
  simp [partialSums]

@[simp]
theorem partialSums_ne_nil [Add α] [Zero α] {l : List α} :
    l.partialSums ≠ [] := by simp [ne_nil_iff_length_pos]

@[simp, grind =]
theorem partialSums_nil [Add α] [Zero α] : ([] : List α).partialSums = [0] := by
  simp [partialSums]

theorem partialSums_cons [Add α] [Zero α] [Std.Associative (α := α) (· + ·)]
    [Std.LawfulIdentity (α := α) (· + ·) 0] {l : List α} :
    (a :: l).partialSums = 0 :: l.partialSums.map (a + ·) := by
  simp only [partialSums, scanl_cons, Std.LawfulLeftIdentity.left_id, cons.injEq]
  induction l generalizing a with
  | nil =>
    simp only [Std.LawfulRightIdentity.right_id, scanl_nil, map_cons, map_nil]
  | cons b l ih =>
    simp [Std.LawfulLeftIdentity.left_id, Std.LawfulRightIdentity.right_id]
    rw [ih (a := b), ih (a := a + b), map_map]
    congr; funext; simp [Std.Associative.assoc]

theorem partialSums_append [Add α] [Zero α] [Std.Associative (α := α) (· + ·)]
    [Std.LawfulIdentity (α := α) (· + ·) 0] {l₁ l₂ : List α} :
    (l₁ ++ l₂).partialSums = l₁.partialSums ++ l₂.partialSums.tail.map (l₁.sum + · ) := by
  induction l₁ generalizing l₂ with
  | nil => cases l₂ <;> simp [partialSums, Std.LawfulLeftIdentity.left_id]
  | cons _ _ ih =>
    simp only [cons_append, partialSums_cons, ih, map_tail, map_append, map_map, sum_cons,
      cons.injEq, append_cancel_left_eq, true_and]
    congr 2; funext; simp [Std.Associative.assoc]

@[simp, grind =]
theorem getElem_partialSums [Add α] [Zero α] [Std.Associative (α := α) (· + ·)]
    [Std.LawfulIdentity (α := α) (· + ·) 0] {l : List α} (h : i < l.partialSums.length) :
    l.partialSums[i] = (l.take i).sum := by
  simp [partialSums, sum_eq_foldl]

@[simp, grind =]
theorem getElem?_partialSums [Add α] [Zero α] [Std.Associative (α := α) (· + ·)]
    [Std.LawfulIdentity (α := α) (· + ·) 0] {l : List α} :
    l.partialSums[i]? = if i ≤ l.length then some (l.take i).sum else none := by
  split <;> grind

@[simp, grind =]
theorem take_partialSums [Add α] [Zero α] {l : List α} :
    l.partialSums.take (i+1) = (l.take i).partialSums := by
  simp [partialSums, take_scanl]

@[simp, grind =]
theorem length_partialProds [Mul α] [One α] {l : List α} :
    l.partialProds.length = l.length + 1 := by
  simp [partialProds]

@[simp, grind =]
theorem partialProds_nil [Mul α] [One α]
  : ([] : List α).partialProds = [1]
  := by simp [partialProds]

theorem partialProds_cons [Mul α] [One α] [Std.Associative (α := α) (· * ·)]
    [Std.LawfulIdentity (α := α) (· * ·) 1] {l : List α} :
    (a :: l).partialProds = 1 :: l.partialProds.map (a * ·) := by
  simp only [partialProds, scanl_cons, Std.LawfulLeftIdentity.left_id, cons.injEq]
  induction l generalizing a with
  | nil =>
    simp only [Std.LawfulRightIdentity.right_id, scanl_nil, map_cons, map_nil]
  | cons b l ih =>
    simp [Std.LawfulLeftIdentity.left_id, Std.LawfulRightIdentity.right_id]
    rw [ih (a := b), ih (a := a * b), map_map]
    congr; funext; simp [Std.Associative.assoc]

theorem partialProds_append [Mul α] [One α] [Std.Associative (α := α) (· * ·)]
    [Std.LawfulIdentity (α := α) (· * ·) 1] {l₁ l₂ : List α} :
    (l₁ ++ l₂).partialProds = l₁.partialProds ++ l₂.partialProds.tail.map (l₁.prod * · ) := by
  induction l₁ generalizing l₂ with
  | nil => cases l₂ <;> simp [partialProds, Std.LawfulLeftIdentity.left_id]
  | cons _ _ ih =>
    simp only [cons_append, partialProds_cons, ih, map_tail, map_append, map_map, prod_cons,
      cons.injEq, append_cancel_left_eq, true_and]
    congr 2; funext; simp [Std.Associative.assoc]

@[simp, grind =]
theorem getElem_partialProds [Mul α] [One α] [Std.Associative (α := α) (· * ·)]
    [Std.LawfulIdentity (α := α) (· * ·) 1] {l : List α} (h : i < l.partialProds.length) :
    l.partialProds[i] = (l.take i).prod := by
  simp [partialProds, prod_eq_foldl]

@[simp, grind =]
theorem getElem?_partialProds [Mul α] [One α] [Std.Associative (α := α) (· * ·)]
    [Std.LawfulIdentity (α := α) (· * ·) 1] {l : List α} :
    l.partialProds[i]? = if i ≤ l.length then some (l.take i).prod else none := by
  split <;> grind

@[simp, grind =]
theorem take_partialProds [Mul α] [One α] {l : List α} :
    l.partialProds.take (i+1) = (l.take i).partialProds := by
  simp [partialProds, take_scanl]

/-! ### flatten -/

theorem length_flatten_mem_partialSums_map_length (L : List (List α)) :
    L.flatten.length ∈ (L.map length).partialSums := by
  induction L with
  | nil => simp
  | cons l L ih =>
    simp [flatten_cons, partialSums_cons]
    right
    simpa using ih

theorem getElem_flatten_aux₁ (L : List (List α)) (i : Nat) (h : i < L.flatten.length) :
    (L.map length).partialSums.findIdx (· > i) - 1 < L.length := by
  have := findIdx_lt_length_of_exists
    (xs := (L.map length).partialSums) (p := fun x => decide (x > i))
  specialize this ⟨L.flatten.length,
    length_flatten_mem_partialSums_map_length L, by grind⟩
  simp at this
  simp
  have : 0 < findIdx (fun x => decide (i < x)) (map length L).partialSums := by
    by_contra w
    simp at w
  omega

theorem getElem_flatten_aux₂ (L : List (List α)) (i : Nat) (h : i < L.flatten.length) :
    let j := (L.map length).partialSums.findIdx (· > i) - 1
    have hj : j < L.length := getElem_flatten_aux₁ L i h
    let k := i - (L.take j).flatten.length
    k < L[j].length := by
  induction L generalizing i with
  | nil => simp at h
  | cons l L ih =>
    simp only [map_cons, partialSums_cons, findIdx_cons, Nat.not_lt_zero, decide_false,
      findIdx_map, Function.comp_def, cond_false, Nat.add_one_sub_one, length_flatten, map_take,
      getElem_cons]
    split <;> rename_i h'
    · simp only [h', take_zero, sum_nil, Nat.sub_zero]
      rw [findIdx_eq (by simp)] at h'
      simp_all
    · have : l.length ≤ i := by
        rw [findIdx_eq (by simp)] at h'
        simp_all
      rw [take_cons (by grind)]
      specialize ih (i - l.length) (by grind)
      have p : ∀ x, i - l.length < x ↔ i < l.length + x := by grind
      simp only [p, length_flatten, map_take] at ih
      grind

/--
Indexing into a flattened list: `L.flatten[i]` equals `L[j][k]` where
`j` is the sublist index and `k` is the offset within that sublist.

The indices are computed as:
- `j` is one less than where the cumulative sum first exceeds `i`
- `k` is `i` minus the total length of the first `j` sublists

This theorem states that these indices are in range and the equality holds.
-/
theorem getElem_flatten (L : List (List α)) (i : Nat) (h : i < L.flatten.length) :
    L.flatten[i] =
      let j := (L.map length).partialSums.findIdx (· > i) - 1
      have hj : j < L.length := getElem_flatten_aux₁ L i h
      let k := i - (L.take j).flatten.length
      have hk : k < L[j].length := getElem_flatten_aux₂ L i h
      L[j][k] := by
  induction L generalizing i with
  | nil => simp at h
  | cons l L ih =>
    simp only [flatten_cons, getElem_append]
    split <;> rename_i h'
    · have : findIdx (fun x => decide (x > i)) (map length (l :: L)).partialSums = 1 := by
        simp [partialSums_cons, findIdx_cons]
        rw [findIdx_eq] <;> grind
      simp only [this]
      simp
    · rw [ih]
      have : findIdx (fun x => decide (x > i)) (map length (l :: L)).partialSums =
          findIdx (fun x => decide (x > i - l.length)) (map length L).partialSums + 1 := by
        simp [partialSums_cons, findIdx_cons, Function.comp_def]
        congr
        funext x
        grind
      simp only [this]
      simp only [getElem_cons]
      split <;> rename_i h''
      · simp [findIdx_eq] at h''
      · congr 1
        rw [take_cons]
        · simp
          omega
        · simp

/--
Taking the first `i` elements of a flattened list
can be expressed as the flattening of the first `j` complete sublists, plus the first
`k` elements of the `j`-th sublist.

The indices are computed as:
- `j` is one less than where the cumulative sum first exceeds `i`
- `k` is `i` minus the total length of the first `j` sublists
-/
proof_wanted take_flatten (L : List (List α)) (i : Nat) :
    let j := (L.map length).partialSums.findIdx (· > i) - 1
    let k := i - (L.take j).flatten.length
    L.flatten.take i = (L.take j).flatten ++ (L[j]?.getD []).take k

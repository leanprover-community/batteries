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

/-! ### scanl -/

/--
Unfold `scanl` once, unconditionally exposing its head.
-/
theorem scanl_unfold_once {f : β → α → β} {init : β} {as : List α} :
    as.scanl f init = init :: match as with | [] => [] | a :: as' => as'.scanl f (f init a) := by
  split <;> simp

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

/--
Unfold `partialSums` once, unconditionally exposing its head.
-/
theorem partialSums_unfold_once [Add α] [Zero α] [Std.Associative (α := α) (· + ·)]
    [Std.LawfulIdentity (α := α) (· + ·) 0] {l : List α} :
    l.partialSums = (0 : α) :: match l with | [] => [] | a :: l' => l'.partialSums.map (a + ·) := by
  split <;> simp [partialSums_cons]

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
      findIdx_map, Function.comp_def, Bool.false_eq_true, ite_false, Nat.add_one_sub_one,
      length_flatten, map_take, getElem_cons]
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
Lemma for `take_flatten` and all related theorems.
Moving the threshold and all elements of `L` upwards by `offset`
does not change the result of `findIdx`.
-/
theorem findIdx_thres_offset (L : List Nat) (offset thres : Nat) :
    L.findIdx (· > thres) =
    (L.map (offset + ·)).findIdx (· > thres + offset) := by
  induction L generalizing offset thres with
  | nil =>
    simp
  | cons head tail tail_ih =>
    simp [findIdx_cons]
    by_cases thres_head : thres < head
    · grind
    · have not_thres_offset_lt_offset_head : ¬(thres + offset < offset + head) := by lia
      simp [thres_head, not_thres_offset_lt_offset_head]
      simp at tail_ih
      apply tail_ih

private theorem take_flatten_helper (L : List (List α)) (i : Nat) :
    let j := (L.map List.length).partialSums.findIdx (· > i) - 1
    let k := i - (L.take j).flatten.length
    (i < L.flatten.length → j < L.length) ∧
    (i < L.flatten.length → (h : j < L.length) → k < L[j].length) ∧
    L.flatten[i]? = L[j]?.bind (·[k]?) ∧
    L.flatten.take i = (L.take j).flatten ++ (L[j]?.getD []).take k ∧
    L.flatten.drop i = (L[j]?.getD []).drop k ++ (L.drop (j + 1)).flatten ∧
    L.flatten.drop i = (L.drop j).flatten.drop k := by
  induction L generalizing i with
  | nil =>
    simp
  | cons head tail tail_ih =>
    rw [map_cons, partialSums_cons, findIdx_cons]
    by_cases i_head_length : i < head.length
    · rw [partialSums_unfold_once, map_cons, findIdx_cons]
      simp [i_head_length]
      -- inequalities are removed by simp; last two statements are discharged with the same line
      constructor <;> try constructor
      · rw [getElem?_append]; simp [i_head_length]
      · rw [take_append_of_le_length (by lia)]
      · rw [drop_append_of_le_length (by lia)]
    · have i_ge_head_length := Nat.le_of_not_lt i_head_length
      -- handle j in both the goal and tail_ih to extract common term
      have ⟨goalJ, goalJ_def⟩ : ∃ j, j =
        ((tail.map length).partialSums.map (head.length + ·)).findIdx (· > i) := by simp
      rw [← goalJ_def]
      specialize tail_ih (i - head.length)
      rw [findIdx_thres_offset _ head.length, Nat.sub_add_cancel i_ge_head_length] at tail_ih
      rw [← goalJ_def] at tail_ih
      -- goalJ is succ
      rw [partialSums_unfold_once] at goalJ_def
      simp [findIdx_cons, i_head_length] at goalJ_def
      have ⟨goalJ', goalJ_succ⟩ : ∃ goalJ', goalJ = goalJ' + 1 := by simp [goalJ_def]
      -- now with this information, the goal is essentially the same as tail_ih
      constructor <;> try constructor <;> try constructor <;> try constructor
      · simp [goalJ_succ]
        intro tail_ih_hyp
        have tail_ih_hyp := Nat.sub_lt_left_of_lt_add (by lia) tail_ih_hyp
        simp [goalJ_succ] at tail_ih
        apply tail_ih.1 tail_ih_hyp
      · simp [goalJ_succ, ← Nat.sub_sub]
        intro tail_ih_hyp
        have tail_ih_hyp := Nat.sub_lt_left_of_lt_add (by lia) tail_ih_hyp
        simp [goalJ_succ] at tail_ih
        apply tail_ih.2.1 tail_ih_hyp
      · simpa [goalJ_succ, getElem?_append,
          i_head_length, ← Nat.sub_sub] using tail_ih.2.2.1
      · simpa [goalJ_succ, take_append,
          take_of_length_le i_ge_head_length, ← Nat.sub_sub]
          using tail_ih.2.2.2.1
      · simpa [goalJ_succ, drop_append,
          drop_of_length_le i_ge_head_length, ← Nat.sub_sub]
          using tail_ih.2.2.2.2

/--
Splitting a flattened list at `i` gives the two parts:
- The flattening of the first `j` complete sublists, plus the first `k` elements of
  the `j`-th sublist, and
- The `j`-th sublist with its first `k` elements removed, plus the flattening of
  the original list with the first `j+1` sublists removed.

The indices are computed as:
- `j` is one less than where the cumulative sum first exceeds `i`
- `k` is `i` minus the total length of the first `j` sublists
-/
theorem splitAt_flatten (L : List (List α)) (i : Nat) :
    let j := (L.map List.length).partialSums.findIdx (· > i) - 1
    let k := i - (L.take j).flatten.length
    L.flatten.splitAt i = (
      (L.take j).flatten ++ (L[j]?.getD []).take k,
      (L[j]?.getD []).drop k ++ (L.drop (j + 1)).flatten
    ) := by
  rw [splitAt_eq, Prod.mk.injEq]
  grind [take_flatten_helper L i]

/--
Taking the first `i` elements of a flattened list
can be expressed as the flattening of the first `j` complete sublists, plus the first
`k` elements of the `j`-th sublist.
-/
theorem take_flatten (L : List (List α)) (i : Nat) :
    let j := (L.map List.length).partialSums.findIdx (· > i) - 1
    let k := i - (L.take j).flatten.length
    L.flatten.take i = (L.take j).flatten ++ (L[j]?.getD []).take k := by
  grind [take_flatten_helper L i]

/--
Dropping the first `i` elements of a flattened list
can be expressed as the `j`-th sublist without its first `k` elements, plus
the flattening of the original list with the first `j+1` sublists removed.
-/
theorem drop_flatten (L : List (List α)) (i : Nat) :
    let j := (L.map List.length).partialSums.findIdx (· > i) - 1
    let k := i - (L.take j).flatten.length
    L.flatten.drop i = (L[j]?.getD []).drop k ++ (L.drop (j + 1)).flatten := by
  grind [take_flatten_helper L i]

/--
Alternatively, dropping the first `i` elements of a flattened list
can be expressed as removing the first `j` sublists, flattening the result,
and then removing its first `k` elements.
-/
theorem drop_flatten' (L : List (List α)) (i : Nat) :
    let j := (L.map List.length).partialSums.findIdx (· > i) - 1
    let k := i - (L.take j).flatten.length
    L.flatten.drop i = (L.drop j).flatten.drop k := by
  grind [take_flatten_helper L i]

theorem getElem?_flatten (L : List (List α)) (i : Nat) :
    let j := (L.map List.length).partialSums.findIdx (· > i) - 1
    let k := i - (L.take j).flatten.length
    L.flatten[i]? = L[j]?.bind (·[k]?) := by
  grind [take_flatten_helper L i]

theorem getElem_j_valid (L : List (List α)) (i : Nat) (h : i < L.flatten.length) :
    let j := (L.map List.length).partialSums.findIdx (· > i) - 1
    j < L.length := by
  grind [take_flatten_helper L i]

theorem getElem_k_valid (L : List (List α)) (i : Nat) (h : i < L.flatten.length) :
    let j := (L.map List.length).partialSums.findIdx (· > i) - 1
    let k := i - (L.take j).flatten.length
    (h' : j < L.length) → k < L[j].length := by
  grind [take_flatten_helper L i]

theorem getElem_flatten' (L : List (List α)) (i : Nat) (h : i < L.flatten.length) :
    let j := (L.map List.length).partialSums.findIdx (· > i) - 1
    let k := i - (L.take j).flatten.length
    have j_valid := getElem_j_valid L i h
    have k_valid := getElem_k_valid L i h j_valid
    L.flatten[i] = L[j][k] := by
  grind [take_flatten_helper L i]

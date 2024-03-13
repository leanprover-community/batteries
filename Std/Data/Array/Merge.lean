/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

namespace Array

/--
Merge arrays `xs` and `ys`, which must be sorted according to `compare`. The
result is sorted as well. If two (or more) elements are equal according to
`compare`, they are preserved.
-/
def mergeSortedPreservingDuplicates [ord : Ord α] (xs ys : Array α) :
    Array α :=
  let acc := Array.mkEmpty (xs.size + ys.size)
  go acc 0 0
where
  /-- Auxiliary definition for `mergeSortedPreservingDuplicates`. -/
  go (acc : Array α) (i j : Nat) : Array α :=
    if hi : i ≥ xs.size then
      acc ++ ys[j:]
    else if hj : j ≥ ys.size then
      acc ++ xs[i:]
    else
      have hi : i < xs.size := Nat.lt_of_not_le hi
      have hj : j < ys.size := Nat.lt_of_not_le hj
      have hij : i + j < xs.size + ys.size := Nat.add_lt_add hi hj
      let x := xs[i]
      let y := ys[j]
      if compare x y |>.isLE then
        have : xs.size + ys.size - (i + 1 + j) < xs.size + ys.size - (i + j) := by
          rw [show i + 1 + j = i + j + 1 by simp_arith]
          exact Nat.sub_succ_lt_self _ _ hij
        go (acc.push x) (i + 1) j
      else
        have : xs.size + ys.size - (i + j + 1) < xs.size + ys.size - (i + j) :=
          Nat.sub_succ_lt_self _ _ hij
        go (acc.push y) i (j + 1)
  termination_by xs.size + ys.size - (i + j)

/--
Merge arrays `xs` and `ys`, which must be sorted according to `compare` and must
not contain duplicates. Equal elements are merged using `merge`. If `merge`
respects the order (i.e. for all `x`, `y`, `y'`, `z`, if `x < y < z` and
`x < y' < z` then `x < merge y y' < z`) then the resulting array is again
sorted.
-/
def mergeSortedMergingDuplicates [ord : Ord α] (xs ys : Array α)
    (merge : α → α → α) : Array α :=
  let acc := Array.mkEmpty (xs.size + ys.size)
  go acc 0 0
where
  /-- Auxiliary definition for `mergeSortedMergingDuplicates`. -/
  go (acc : Array α) (i j : Nat) : Array α :=
    if hi : i ≥ xs.size then
      acc ++ ys[j:]
    else if hj : j ≥ ys.size then
      acc ++ xs[i:]
    else
      have hi : i < xs.size := Nat.lt_of_not_le hi
      have hj : j < ys.size := Nat.lt_of_not_le hj
      have hij : i + j < xs.size + ys.size := Nat.add_lt_add hi hj
      let x := xs[i]
      let y := ys[j]
      match compare x y with
      | Ordering.lt =>
        have : xs.size + ys.size - (i + 1 + j) < xs.size + ys.size - (i + j) := by
          rw [show i + 1 + j = i + j + 1 by simp_arith]
          exact Nat.sub_succ_lt_self _ _ hij
        go (acc.push x) (i + 1) j
      | Ordering.gt =>
        have : xs.size + ys.size - (i + j + 1) < xs.size + ys.size - (i + j) :=
          Nat.sub_succ_lt_self _ _ hij
        go (acc.push y) i (j + 1)
      | Ordering.eq =>
        have : xs.size + ys.size - (i + 1 + (j + 1)) < xs.size + ys.size - (i + j) := by
          rw [show i + 1 + (j + 1) = i + j + 2 by simp_arith]
          apply Nat.sub_add_lt_sub _ (by decide)
          rw [show i + j + 2 = (i + 1) + (j + 1) by simp_arith]
          exact Nat.add_le_add hi hj
        go (acc.push (merge x y)) (i + 1) (j + 1)
    termination_by xs.size + ys.size - (i + j)

/--
Merge arrays `xs` and `ys`, which must be sorted according to `compare` and must
not contain duplicates. If an element appears in both `xs` and `ys`, only one
copy is kept.
-/
@[inline]
def mergeSortedDeduplicating [ord : Ord α] (xs ys : Array α) : Array α :=
  mergeSortedMergingDuplicates (ord := ord) xs ys fun x _ => x

set_option linter.unusedVariables false in
/--
Merge `xs` and `ys`, which do not need to be sorted. Elements which occur in
both `xs` and `ys` are only added once. If `xs` and `ys` do not contain
duplicates, then neither does the result. O(n*m)!
-/
def mergeUnsortedDeduplicating [eq : BEq α] (xs ys : Array α) : Array α :=
  -- Ideally we would check whether `xs` or `ys` have spare capacity, to prevent
  -- copying if possible. But Lean arrays don't expose their capacity.
  if xs.size < ys.size then go ys xs else go xs ys
where
  /-- Auxiliary definition for `mergeUnsortedDeduplicating`. -/
  @[inline]
  go (xs ys : Array α) :=
    let xsSize := xs.size
    ys.foldl (init := xs) fun xs y =>
      if xs.any (· == y) (stop := xsSize) then xs else xs.push y

/--
Replace each run `[x₁, ⋯, xₙ]` of equal elements in `xs` with
`f ⋯ (f (f x₁ x₂) x₃) ⋯ xₙ`.
-/
def mergeAdjacentDuplicates [eq : BEq α] (f : α → α → α) (xs : Array α) :
    Array α :=
  if h : 0 < xs.size then go #[] 1 (xs.get ⟨0, h⟩) else xs
where
  /-- Auxiliary definition for `mergeAdjacentDuplicates`. -/
  go (acc : Array α) (i : Nat) (hd : α) :=
    if h : i < xs.size then
      let x := xs[i]
      if x == hd then
        go acc (i + 1) (f hd x)
      else
        go (acc.push hd) (i + 1) x
    else
      acc.push hd
  termination_by xs.size - i

/--
Deduplicate a sorted array. The array must be sorted with to an order which
agrees with `==`, i.e. whenever `x == y` then `compare x y == .eq`.
-/
def deduplicateSorted [eq : BEq α] (xs : Array α) : Array α :=
  xs.mergeAdjacentDuplicates (eq := eq) fun x _ => x

/--
Sort and deduplicate an array.
-/
def sortAndDeduplicate [ord : Ord α] (xs : Array α) : Array α :=
  have := ord.toBEq
  deduplicateSorted <| xs.qsort (compare · · |>.isLT)

end Array

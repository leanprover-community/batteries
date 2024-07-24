/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/
import Batteries.Tactic.Alias

namespace Array

/--
`O(|xs| + |ys|)`. Merge arrays `xs` and `ys`. If the arrays are sorted according to `lt`, then the
result is sorted as well. If two (or more) elements are equal according to `lt`, they are preserved.
-/
def merge (lt : α → α → Bool) (xs ys : Array α) : Array α :=
  go (Array.mkEmpty (xs.size + ys.size)) 0 0
where
  /-- Auxiliary definition for `merge`. -/
  go (acc : Array α) (i j : Nat) : Array α :=
    if hi : i ≥ xs.size then
      acc ++ ys[j:]
    else if hj : j ≥ ys.size then
      acc ++ xs[i:]
    else
      let x := xs[i]
      let y := ys[j]
      if lt x y then go (acc.push x) (i + 1) j else go (acc.push y) i (j + 1)
  termination_by xs.size + ys.size - (i + j)

set_option linter.unusedVariables false in
@[deprecated merge (since := "2024-04-24"), inherit_doc merge]
def mergeSortedPreservingDuplicates [ord : Ord α] (xs ys : Array α) : Array α :=
  merge (compare · · |>.isLT) xs ys

/--
`O(|xs| + |ys|)`. Merge arrays `xs` and `ys`, which must be sorted according to `compare` and must
not contain duplicates. Equal elements are merged using `merge`. If `merge` respects the order
(i.e. for all `x`, `y`, `y'`, `z`, if `x < y < z` and `x < y' < z` then `x < merge y y' < z`)
then the resulting array is again sorted.
-/
def mergeDedupWith [ord : Ord α] (xs ys : Array α) (merge : α → α → α) : Array α :=
  go (Array.mkEmpty (xs.size + ys.size)) 0 0
where
  /-- Auxiliary definition for `mergeDedupWith`. -/
  go (acc : Array α) (i j : Nat) : Array α :=
    if hi : i ≥ xs.size then
      acc ++ ys[j:]
    else if hj : j ≥ ys.size then
      acc ++ xs[i:]
    else
      let x := xs[i]
      let y := ys[j]
      match compare x y with
      | .lt => go (acc.push x) (i + 1) j
      | .gt => go (acc.push y) i (j + 1)
      | .eq => go (acc.push (merge x y)) (i + 1) (j + 1)
  termination_by xs.size + ys.size - (i + j)

@[deprecated (since := "2024-04-24")] alias mergeSortedMergingDuplicates := mergeDedupWith

/--
`O(|xs| + |ys|)`. Merge arrays `xs` and `ys`, which must be sorted according to `compare` and must
not contain duplicates. If an element appears in both `xs` and `ys`, only one copy is kept.
-/
@[inline] def mergeDedup [ord : Ord α] (xs ys : Array α) : Array α :=
  mergeDedupWith (ord := ord) xs ys fun x _ => x

@[deprecated (since := "2024-04-24")] alias mergeSortedDeduplicating := mergeDedup

set_option linter.unusedVariables false in
/--
`O(|xs| * |ys|)`. Merge `xs` and `ys`, which do not need to be sorted. Elements which occur in
both `xs` and `ys` are only added once. If `xs` and `ys` do not contain duplicates, then neither
does the result.
-/
def mergeUnsortedDedup [eq : BEq α] (xs ys : Array α) : Array α :=
  -- Ideally we would check whether `xs` or `ys` have spare capacity, to prevent
  -- copying if possible. But Lean arrays don't expose their capacity.
  if xs.size < ys.size then go ys xs else go xs ys
where
  /-- Auxiliary definition for `mergeUnsortedDedup`. -/
  @[inline] go (xs ys : Array α) :=
    let xsSize := xs.size
    ys.foldl (init := xs) fun xs y =>
      if xs.any (· == y) (stop := xsSize) then xs else xs.push y

@[deprecated (since := "2024-04-24")] alias mergeUnsortedDeduplicating := mergeUnsortedDedup

/--
`O(|xs|)`. Replace each run `[x₁, ⋯, xₙ]` of equal elements in `xs` with
`f ⋯ (f (f x₁ x₂) x₃) ⋯ xₙ`.
-/
def mergeAdjacentDups [eq : BEq α] (f : α → α → α) (xs : Array α) : Array α :=
  if h : 0 < xs.size then go (mkEmpty xs.size) 1 (xs.get ⟨0, h⟩) else xs
where
  /-- Auxiliary definition for `mergeAdjacentDups`. -/
  go (acc : Array α) (i : Nat) (hd : α) :=
    if h : i < xs.size then
      let x := xs[i]
      if x == hd then go acc (i + 1) (f hd x) else go (acc.push hd) (i + 1) x
    else
      acc.push hd
  termination_by xs.size - i

@[deprecated (since := "2024-04-24")] alias mergeAdjacentDuplicates := mergeAdjacentDups

/--
`O(|xs|)`. Deduplicate a sorted array. The array must be sorted with to an order which agrees with
`==`, i.e. whenever `x == y` then `compare x y == .eq`.
-/
def dedupSorted [eq : BEq α] (xs : Array α) : Array α :=
  xs.mergeAdjacentDups (eq := eq) fun x _ => x

@[deprecated (since := "2024-04-24")] alias deduplicateSorted := dedupSorted

/-- `O(|xs| log |xs|)`. Sort and deduplicate an array. -/
def sortDedup [ord : Ord α] (xs : Array α) : Array α :=
  have := ord.toBEq
  dedupSorted <| xs.qsort (compare · · |>.isLT)

@[deprecated (since := "2024-04-24")] alias sortAndDeduplicate := sortDedup

end Array

/-
Copyright (c) 2021 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Paulino, Floris van Doorn, Jannis Limperg
-/
import Std.Data.Array.Init.Basic
import Std.Data.Ord

/-!
## Definitions on Arrays

This file contains various definitions on `Array`. It does not contain
proofs about these definitions, those are contained in other files in `Std.Data.Array`.
-/

namespace Array

/-- The array `#[0, 1, ..., n - 1]`. -/
def range (n : Nat) : Array Nat :=
  n.fold (flip Array.push) #[]

/-- Drop `none`s from a Array, and replace each remaining `some a` with `a`. -/
def reduceOption (l : Array (Option α)) : Array α :=
  l.filterMap id

/-- Turns `#[#[a₁, a₂, ⋯], #[b₁, b₂, ⋯], ⋯]` into `#[a₁, a₂, ⋯, b₁, b₂, ⋯]` -/
def flatten (arr : Array (Array α)) : Array α :=
  arr.foldl (init := #[]) fun acc a => acc.append a

/-- Turns `#[a, b]` into `#[(a, 0), (b, 1)]`. -/
def zipWithIndex (arr : Array α) : Array (α × Nat) :=
  arr.mapIdx fun i a => (a, i)

/--
Check whether `xs` and `ys` are equal as sets, i.e. they contain the same
elements when disregarding order and duplicates. `O(n*m)`! If your element type
has an `Ord` instance, it is asymptotically more efficient to sort the two
arrays, remove duplicates and then compare them elementwise.
-/
def equalSet [BEq α] (xs ys : Array α) : Bool :=
  xs.all (ys.contains ·) && ys.all (xs.contains ·)

set_option linter.unusedVariables.funArgs false in
/--
Sort an array using `compare` to compare elements.
-/
def qsortOrd [ord : Ord α] (xs : Array α) : Array α :=
  xs.qsort λ x y => compare x y |>.isLT

set_option linter.unusedVariables.funArgs false in
/--
Find the first minimal element of an array. If the array is empty, `d` is
returned. If `start` and `stop` are given, only the subarray `xs[start:stop]` is
considered.
-/
@[inline]
protected def minD [ord : Ord α]
    (xs : Array α) (d : α) (start := 0) (stop := xs.size) : α :=
  xs.foldl (init := d) (start := start) (stop := stop) λ min x =>
    if compare x min |>.isLT then x else min

set_option linter.unusedVariables.funArgs false in
/--
Find the first minimal element of an array. If the array is empty, `none` is
returned. If `start` and `stop` are given, only the subarray `xs[start:stop]` is
considered.
-/
@[inline]
protected def min? [ord : Ord α]
    (xs : Array α) (start := 0) (stop := xs.size) : Option α :=
  if h : start < xs.size then
    some $ xs.minD (xs.get ⟨start, h⟩) start stop
  else
    none

set_option linter.unusedVariables.funArgs false in
/--
Find the first minimal element of an array. If the array is empty, `default` is
returned. If `start` and `stop` are given, only the subarray `xs[start:stop]` is
considered.
-/
@[inline]
protected def minI [ord : Ord α] [Inhabited α]
    (xs : Array α) (start := 0) (stop := xs.size) : α :=
  xs.minD default start stop

set_option linter.unusedVariables.funArgs false in
/--
Find the first maximal element of an array. If the array is empty, `d` is
returned. If `start` and `stop` are given, only the subarray `xs[start:stop]` is
considered.
-/
@[inline]
protected def maxD [ord : Ord α]
    (xs : Array α) (d : α) (start := 0) (stop := xs.size) : α :=
  xs.minD (ord := ord.opposite) d start stop

set_option linter.unusedVariables.funArgs false in
/--
Find the first maximal element of an array. If the array is empty, `none` is
returned. If `start` and `stop` are given, only the subarray `xs[start:stop]` is
considered.
-/
@[inline]
protected def max? [ord : Ord α]
    (xs : Array α) (start := 0) (stop := xs.size) : Option α :=
  xs.min? (ord := ord.opposite) start stop

set_option linter.unusedVariables.funArgs false in
/--
Find the first maximal element of an array. If the array is empty, `default` is
returned. If `start` and `stop` are given, only the subarray `xs[start:stop]` is
considered.
-/
@[inline]
protected def maxI [ord : Ord α] [Inhabited α]
    (xs : Array α) (start := 0) (stop := xs.size) : α :=
  xs.minI (ord := ord.opposite) start stop

/--
Returns the first and all the rest of the elements of the array.
-/
protected def splitFront (xs : Array α) (h : 0 < xs.size) : α × Array α :=
  let head := xs.get ⟨0, h⟩
  let tail := Subarray.mk xs 1 xs.size (Nat.succ_le_of_lt h) (Nat.le_refl _) |>.toArray
  (head, tail)

/--
Returns the first and all the rest of the elements of the array, or `none` if it is empty.
-/
protected def splitFront? (xs : Array α) : Option (α × Array α) :=
  if h : 0 < xs.size then
    some <| xs.splitFront h
  else
    none

/--
Returns the last and all the rest of the elements of the array.
-/
protected def splitLast (xs : Array α) (h : 0 < xs.size) : Array α × α :=
  have h2 := Nat.sub_lt h (by decide)
  let last := xs[xs.size - 1]'h2
  let heads := xs.pop
  (heads, last)

/--
Returns the last and all the rest of the elements of the array, or `none` if it is empty.
-/
protected def splitLast? (xs : Array α) : Option (Array α × α) :=
  if h : 0 < xs.size then
    some <| xs.splitLast h
  else
    none

/--
Returns the first element of the array.
-/
protected def front (xs : Array α) (h : 0 < xs.size) : α :=
  xs.get ⟨0, h⟩

/--
Returns the first element of the array, or `none` if it is empty.
-/
protected def front? (xs : Array α) : Option α :=
  if h : 0 < xs.size then
    some <| xs.front h
  else
    none

/--
Split an array apart into two arrays at a given index. The first half
will contain all values from `[0, mid)`, the second will contain `[mid, xs.size)`.
Notably if `mid` is out of bounds for `xs` the function will return `(xs, #[])`.
-/
protected def splitAt (xs : Array α) (mid : Nat) : Array α × Array α :=
  if h : mid ≤ xs.size then
    let rhs := Subarray.mk xs mid xs.size h (Nat.le_refl _) |>.toArray
    let lhs := xs.shrink mid
    (lhs, rhs)
  else
    (xs, #[])

end Array


namespace Subarray

/--
The empty subarray.
-/
protected def empty : Subarray α where
  as := #[]
  start := 0
  stop := 0
  h₁ := Nat.le_refl 0
  h₂ := Nat.le_refl 0

instance : EmptyCollection (Subarray α) :=
  ⟨Subarray.empty⟩

instance : Inhabited (Subarray α) :=
  ⟨{}⟩

/--
Check whether a subarray is empty.
-/
@[inline]
def isEmpty (as : Subarray α) : Bool :=
  as.start == as.stop

/--
Check whether a subarray contains an element.
-/
@[inline]
def contains [BEq α] (as : Subarray α) (a : α) : Bool :=
  as.any (· == a)

/--
Remove the first element of a subarray. Returns the element and the remaining
subarray, or `none` if the subarray is empty.
-/
def popHead? (as : Subarray α) : Option (α × Subarray α) :=
  if h : as.start < as.stop
    then
      let head := as.as.get ⟨as.start, Nat.lt_of_lt_of_le h as.h₂⟩
      let tail :=
        { as with
          start := as.start + 1
          h₁ := Nat.le_of_lt_succ $ Nat.succ_lt_succ h  }
      some (head, tail)
    else
      none

end Subarray

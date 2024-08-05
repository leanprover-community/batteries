/-
Copyright (c) 2021 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Paulino, Floris van Doorn, Jannis Limperg
-/
import Batteries.Data.Array.Init.Lemmas

/-!
## Definitions on Arrays

This file contains various definitions on `Array`. It does not contain
proofs about these definitions, those are contained in other files in `Batteries.Data.Array`.
-/

namespace Array

/-- Drop `none`s from a Array, and replace each remaining `some a` with `a`. -/
def reduceOption (l : Array (Option α)) : Array α :=
  l.filterMap id

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
  xs.qsort fun x y => compare x y |>.isLT

set_option linter.unusedVariables.funArgs false in
/--
Returns the first minimal element among `d` and elements of the array.
If `start` and `stop` are given, only the subarray `xs[start:stop]` is
considered (in addition to `d`).
-/
@[inline]
protected def minWith [ord : Ord α]
    (xs : Array α) (d : α) (start := 0) (stop := xs.size) : α :=
  xs.foldl (init := d) (start := start) (stop := stop) fun min x =>
    if compare x min |>.isLT then x else min

set_option linter.unusedVariables.funArgs false in
/--
Find the first minimal element of an array. If the array is empty, `d` is
returned. If `start` and `stop` are given, only the subarray `xs[start:stop]` is
considered.
-/
@[inline]
protected def minD [ord : Ord α]
    (xs : Array α) (d : α) (start := 0) (stop := xs.size) : α :=
  if h: start < xs.size ∧ start < stop then
    xs.minWith (xs.get ⟨start, h.left⟩) (start + 1) stop
  else
    d

set_option linter.unusedVariables.funArgs false in
/--
Find the first minimal element of an array. If the array is empty, `none` is
returned. If `start` and `stop` are given, only the subarray `xs[start:stop]` is
considered.
-/
@[inline]
protected def min? [ord : Ord α]
    (xs : Array α) (start := 0) (stop := xs.size) : Option α :=
  if h : start < xs.size ∧ start < stop then
    some $ xs.minD (xs.get ⟨start, h.left⟩) start stop
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
Returns the first maximal element among `d` and elements of the array.
If `start` and `stop` are given, only the subarray `xs[start:stop]` is
considered (in addition to `d`).
-/
@[inline]
protected def maxWith [ord : Ord α]
    (xs : Array α) (d : α) (start := 0) (stop := xs.size) : α :=
  xs.minWith (ord := ord.opposite) d start stop

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
`O(|join L|)`. `join L` concatenates all the arrays in `L` into one array.
* `join #[#[a], #[], #[b, c], #[d, e, f]] = #[a, b, c, d, e, f]`
-/
@[inline] def join (l : Array (Array α)) : Array α := l.foldl (· ++ ·) #[]

/-!
### Safe Nat Indexed Array functions
The functions in this section offer variants of Array functions which use `Nat` indices
instead of `Fin` indices. All these functions have as parameter a proof that the index is
valid for the array. But this parameter has a default argument `by get_elem_tactic` which
should prove the index bound.
-/

/--
`setN a i h x` sets an element in a vector using a Nat index which is provably valid.
A proof by `get_elem_tactic` is provided as a default argument for `h`.
This will perform the update destructively provided that `a` has a reference count of 1 when called.
-/
def setN (a : Array α) (i : Nat) (h : i < a.size := by get_elem_tactic) (x : α) : Array α :=
  a.set ⟨i, h⟩ x

/--
`swapN a i j hi hj` swaps two `Nat` indexed entries in an `Array α`.
Uses `get_elem_tactic` to supply a proof that the indices are in range.
`hi` and `hj` are both given a default argument `by get_elem_tactic`.
This will perform the update destructively provided that `a` has a reference count of 1 when called.
-/
def swapN (a : Array α) (i j : Nat)
    (hi : i < a.size := by get_elem_tactic) (hj : j < a.size := by get_elem_tactic) : Array α :=
  Array.swap a ⟨i,hi⟩ ⟨j, hj⟩

/--
`swapAtN a i h x` swaps the entry with index `i : Nat` in the vector for a new entry `x`.
The old entry is returned alongwith the modified vector.
Automatically generates proof of `i < a.size` with `get_elem_tactic` where feasible.
-/
def swapAtN (a : Array α) (i : Nat) (h : i < a.size := by get_elem_tactic) (x : α) : α × Array α :=
  swapAt a ⟨i,h⟩ x

/--
`eraseIdxN a i h` Removes the element at position `i` from a vector of length `n`.
`h : i < a.size` has a default argument `by get_elem_tactic` which tries to supply a proof
that the index is valid.
This function takes worst case O(n) time because it has to backshift all elements at positions
greater than i.
-/
def eraseIdxN (a : Array α) (i : Nat) (h : i < a.size := by get_elem_tactic) : Array α :=
  a.feraseIdx ⟨i, h⟩

end Array


namespace Subarray

/--
The empty subarray.
-/
protected def empty : Subarray α where
  array := #[]
  start := 0
  stop := 0
  start_le_stop := Nat.le_refl 0
  stop_le_array_size := Nat.le_refl 0

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
      let head := as.array.get ⟨as.start, Nat.lt_of_lt_of_le h as.stop_le_array_size⟩
      let tail :=
        { as with
          start := as.start + 1
          start_le_stop := Nat.le_of_lt_succ $ Nat.succ_lt_succ h }
      some (head, tail)
    else
      none

end Subarray

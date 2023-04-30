/-
Copyright (c) 2021 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Paulino, Floris van Doorn, Jannis Limperg, Henrik Böving, Mario Carneiro
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

/--
Find the first maximal element of an array. If the array is empty, `d` is
returned. If `start` and `stop` are given, only the subarray `xs[start:stop]` is
considered.
-/
@[inline]
protected def maxD [ord : Ord α]
    (xs : Array α) (d : α) (start := 0) (stop := xs.size) : α :=
  xs.minD (ord := ord.opposite) d start stop

/--
Find the first maximal element of an array. If the array is empty, `none` is
returned. If `start` and `stop` are given, only the subarray `xs[start:stop]` is
considered.
-/
@[inline]
protected def max? [ord : Ord α]
    (xs : Array α) (start := 0) (stop := xs.size) : Option α :=
  xs.min? (ord := ord.opposite) start stop

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
A stream over arrays. It returns overlapping `Subarray`s of size `size`.

This structure is created by `windows`.
For a dependently typed version that has a proof of this invariant see
`windowsDep`.
-/
structure Windows (α : Type u) where
  /-- The underlying array. -/
  as : Array α
  /-- How big the windows are. -/
  size : Nat
  /-- Where we currently are in the array. -/
  pos : Nat

instance : ToStream (Windows α) (Windows α) where
  toStream w := w

instance : Stream (Windows α) (Subarray α) where
  next? w :=
    if h : w.size + w.pos ≤ w.as.size then
      let arr := Subarray.mk w.as w.pos (w.size + w.pos) (Nat.le_add_left ..) h
      some (arr, { w with pos := w.pos + 1 })
    else
      none

/--
Returns a stream over all contiguous windows of length `size`.
The windows overlap. If the array is shorter than `size`, the stream
returns no values.

For a dependently typed version that has a proof of this invariant see
`windowsDep`.
-/
@[inline] protected def windows (xs : Array α) (size : Nat) : Windows α := ⟨xs, size, 0⟩

/--
A stream over arrays. It returns overlapping `{ xs : Subarray α // xs.size = size }`.

This structure is created by `windowsDep`.
For a non dependently typed version see `Windows`.
-/
structure WindowsDep (as : Array α) (size : Nat) where
  /-- How big the windows are. -/
  pos : Nat

instance : ToStream (WindowsDep as sz) (WindowsDep as sz) where
  toStream w := w

instance (as : Array α) : Stream (WindowsDep as sz) { xs : Subarray α // xs.size = sz } where
  next? := fun ⟨pos⟩ =>
    if h : sz + pos ≤ as.size then
      let arr := Subarray.mk as pos (sz + pos) (Nat.le_add_left ..) h
      some (⟨arr, by rw [Subarray.size, Nat.add_sub_cancel]⟩, ⟨pos + 1⟩)
    else
      none

/--
Returns a stream over all contiguous windows of length `size`.
The windows overlap. If the array is shorter than `size`, the stream
returns no values.
For a non dependently typed version see `windows`.
-/
@[inline] protected def windowsDep (xs : Array α) (size : Nat) : WindowsDep xs size := ⟨0⟩

/--
A stream over an array. It reurns (non-overlapping) chunks (`size` elements at a time),
starting at the beginning of the array.

When the array size is not evenly divided by the chunk size, the last
chunk will be smaller than `size`.

This structure is created by `chunks`.
-/
structure Chunks (α : Type u) where
  /-- The underlying array. -/
  as : Array α
  /-- How big the chunks are. -/
  size : Nat
  /-- If the `size` is 0 we do not progress. -/
  hsz : 0 < size
  /-- Where we currently are in the array. -/
  pos : Nat
  /-- We are in bounds of the array. -/
  hpos : pos ≤ as.size

/--
Returns a stream over `size` elements of the array at a time,
starting at the beginning of the array.
The chunks are `Subarray`s and do not overlap. If `size` does not divide
the length of the array, then the last chunk will be smaller than `size`.

See `chunksExact` for a variant of this stream that returns chunks
of always exactly `size` elements.
-/
@[inline] def chunks (xs : Array α) (size : Nat) (h : 0 < size := by decide) : Chunks α :=
  ⟨xs, size, h, 0, Nat.zero_le _⟩

instance : ToStream (Chunks α) (Chunks α) where
  toStream c := c

instance : Stream (Chunks α) (Subarray α) where
  next? c :=
    if h : c.pos + c.size ≤ c.as.size then
      let arr := Subarray.mk c.as c.pos (c.pos + c.size) (Nat.le_add_right ..) h
      some (arr, { c with pos := c.pos + c.size, hpos := h })
    else if h : c.pos < c.as.size then
      let arr := Subarray.mk c.as c.pos c.as.size (Nat.le_of_lt h) (Nat.le_refl _)
      some (arr, { c with pos := c.as.size, hpos := Nat.le_refl _ })
    else
      none
/--
A stream over an array in (non-overlapping) chunks (`size` elements at a time),
starting at the beginning of the array.

When the array size is not evenly divided by the chunk size, the last up
to `size-1` elements will be omitted.

This structure is created by `chunksExact`.
For a non dependently typed version see `Chunks`.
-/
structure ChunksExact (α : Type u) where
  /-- The underlying array. -/
  as : Array α
  /-- How big the chunks are. -/
  size : Nat
  /-- If the `size` is 0 we do not progress. -/
  h : 0 < size
  /-- Where we currently are in the array. -/
  pos : Nat
  /-- We are in bounds of the array. -/
  hpos : pos ≤ as.size

/--
Returns a stream over `size` elements of the array at a time, starting
at the beginning of the array.

The chunks are `Subarray`s and do not overlap. If `size` does not divide
the length of the array, then the last up to `size-1` elements will be
omitted.

See `chunks` for a variant of this stream that also returns the remainder
as a smaller chunk and `chunksExactDep` for an a stream that encodes the
`size` invariant in its result. See `chunksExact!` for a variant that avoids
the `0 < size` restriction.
-/
@[inline] def chunksExact (xs : Array α) (size : Nat) (h : 0 < size := by decide) :
    ChunksExact α := ⟨xs, size, h, 0, Nat.zero_le _⟩

/--
Returns a stream over `size` elements of the array at a time, starting
at the beginning of the array.

This function is like `chunksExact` but does not require that `size > 0`.
When `size = 0` it returns an empty stream.
-/
@[inline] def chunksExact! (xs : Array α) (size : Nat) : ChunksExact α :=
  if h : 0 < size then chunksExact xs size h else ⟨xs, 1, by decide, xs.size, Nat.le_refl _⟩

instance : ToStream (ChunksExact α) (ChunksExact α) where
  toStream c := c

instance : Stream (ChunksExact α) (Subarray α) where
  next? c :=
    if h : c.pos + c.size ≤ c.as.size then
      let arr := Subarray.mk c.as c.pos (c.pos + c.size) (Nat.le_add_right ..) h
      some (arr, { c with pos := c.pos + c.size, hpos := h })
    else
      none

/--
A stream over an array in (non-overlapping) chunks (`size` elements at a time),
starting at the beginning of the array. The `size` invariant is encoded
as: `{ xs : // Subarrray α // xs.size = size }`.

When the array size is not evenly divided by the chunk size, the last up
to `size-1` elements will be omitted.

This structure is created by `chunksExactDep`.
For a non dependently typed version see `ChunksExact`.
-/
structure ChunksExactDep (as : Array α) (size : Nat) (h : 0 < size) where
  /-- Where we currently are in the array. -/
  pos : Nat
  /-- We are in bounds of the array. -/
  hpos : pos ≤ as.size

/--
Returns a stream over `size` elements of the array at a time, starting
at the beginning of the array.

The chunks are `{ xs : // Subarrray α // xs.size = size }` and do not overlap.
If `size` does not divide the length of the array, then the last up to
`size-1` elements will be omitted.

See `chunks` for a variant of this stream that also returns the remainder
as a smaller chunk and `chunksExact` for a non dependently typed version.
-/
@[inline] def chunksExactDep (xs : Array α) (size : Nat) (h : 0 < size := by decide) :
    ChunksExactDep xs size h := ⟨0, Nat.zero_le _⟩

instance : ToStream (ChunksExactDep as sz h) (ChunksExactDep as sz h) where
  toStream c := c

instance (as : Array α) : Stream (ChunksExactDep as sz h) { xs : Subarray α // xs.size = sz } where
  next? := fun ⟨pos, _⟩ =>
    if h1 : pos + sz ≤ as.size then
      let arr := Subarray.mk as pos (pos + sz) (Nat.le_add_right ..) h1
      some (⟨arr, by rw [Subarray.size, Nat.add_sub_cancel_left]⟩, ⟨pos + sz, h1⟩)
    else
      none

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

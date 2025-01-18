/-
Copyright (c) 2024 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas, François G. Dorais
-/

import Batteries.Data.Array
import Batteries.Data.List.Basic
import Batteries.Data.List.Lemmas
import Batteries.Tactic.Alias
import Batteries.Tactic.Lint.Misc
import Batteries.Tactic.PrintPrefix

/-!
# Vectors

`Vector α n` is a thin wrapper around `Array α` for arrays of fixed size `n`.
-/

namespace Vector

@[deprecated (since := "2024-10-15")] alias size_eq := size_toArray

@[deprecated (since := "2024-11-25")] alias setN := set

@[deprecated (since := "2024-11-25")] alias setD := setIfInBounds

@[deprecated (since := "2024-11-24")] alias swapN := swap

@[deprecated (since := "2024-11-24")] alias swap! := swapIfInBounds

/-- The empty vector. -/
@[inline] def empty : Vector α 0 := ⟨.empty, rfl⟩

/-- Make an empty vector with pre-allocated capacity. -/
@[inline] def mkEmpty (capacity : Nat) : Vector α 0 := ⟨.mkEmpty capacity, rfl⟩

/-- Makes a vector of size `n` with all cells containing `v`. -/
@[inline] def mkVector (n) (v : α) : Vector α n := ⟨mkArray n v, by simp⟩

/-- Returns a vector of size `1` with element `v`. -/
@[inline] def singleton (v : α) : Vector α 1 := ⟨#[v], rfl⟩

instance [Inhabited α] : Inhabited (Vector α n) where
  default := mkVector n default

/-- Get an element of a vector using a `Fin` index. -/
@[inline] def get (v : Vector α n) (i : Fin n) : α :=
  v.toArray[(i.cast v.size_toArray.symm).1]

/-- Get an element of a vector using a `USize` index and a proof that the index is within bounds. -/
@[inline] def uget (v : Vector α n) (i : USize) (h : i.toNat < n) : α :=
  v.toArray.uget i (v.size_toArray.symm ▸ h)

instance : GetElem (Vector α n) Nat α fun _ i => i < n where
  getElem x i h := get x ⟨i, h⟩

/--
Get an element of a vector using a `Nat` index. Returns the given default value if the index is out
of bounds.
-/
@[inline] def getD (v : Vector α n) (i : Nat) (default : α) : α := v.toArray.getD i default

/-- The last element of a vector. Panics if the vector is empty. -/
@[inline] def back! [Inhabited α] (v : Vector α n) : α := v.toArray.back!

/-- The last element of a vector, or `none` if the array is empty. -/
@[inline] def back? (v : Vector α n) : Option α := v.toArray.back?

/-- The last element of a non-empty vector. -/
@[inline] def back [NeZero n] (v : Vector α n) : α :=
  -- TODO: change to just `v[n]`
  have : Inhabited α := ⟨v[0]'(Nat.pos_of_neZero n)⟩
  v.back!

/-- The first element of a non-empty vector.  -/
@[inline] def head [NeZero n] (v : Vector α n) := v[0]'(Nat.pos_of_neZero n)

/-- Push an element `x` to the end of a vector. -/
@[inline] def push (x : α) (v : Vector α n)  : Vector α (n + 1) :=
  ⟨v.toArray.push x, by simp⟩

/-- Remove the last element of a vector. -/
@[inline] def pop (v : Vector α n) : Vector α (n - 1) :=
  ⟨Array.pop v.toArray, by simp⟩

/--
Set an element in a vector using a `Fin` index.

This will perform the update destructively provided that the vector has a reference count of 1.
-/
@[inline] def set (v : Vector α n) (i : Fin n) (x : α) : Vector α n :=
  ⟨v.toArray.set (i.cast v.size_toArray.symm) x, by simp⟩

/--
Set an element in a vector using a `Nat` index. By default, the `get_elem_tactic` is used to
synthesize a proof that the index is within bounds.

This will perform the update destructively provided that the vector has a reference count of 1.
-/
@[inline] def setN (v : Vector α n) (i : Nat) (x : α) (h : i < n := by get_elem_tactic) :
    Vector α n := ⟨v.toArray.setN i x (by simp_all), by simp⟩

/--
Set an element in a vector using a `Nat` index. Returns the vector unchanged if the index is out of
bounds.

This will perform the update destructively provided that the vector has a reference count of 1.
-/
@[inline] def setD (v : Vector α n) (i : Nat) (x : α) : Vector α n :=
  ⟨v.toArray.setD i x, by simp⟩

/--
Set an element in a vector using a `Nat` index. Panics if the index is out of bounds.

This will perform the update destructively provided that the vector has a reference count of 1.
-/
@[inline] def set! (v : Vector α n) (i : Nat) (x : α) : Vector α n :=
  ⟨v.toArray.set! i x, by simp⟩

/-- Append two vectors. -/
@[inline] def append (v : Vector α n) (w : Vector α m) : Vector α (n + m) :=
  ⟨v.toArray ++ w.toArray, by simp⟩

instance : HAppend (Vector α n) (Vector α m) (Vector α (n + m)) where
  hAppend := append

/-- Creates a vector from another with a provably equal length. -/
@[inline] protected def cast (h : n = m) (v : Vector α n) : Vector α m :=
  ⟨v.toArray, by simp [*]⟩

/--
Extracts the slice of a vector from indices `start` to `stop` (exclusive). If `start ≥ stop`, the
result is empty. If `stop` is greater than the size of the vector, the size is used instead.
-/
@[inline] def extract (v : Vector α n) (start stop : Nat) : Vector α (min stop n - start) :=
  ⟨v.toArray.extract start stop, by simp⟩

/-- Maps elements of a vector using the function `f`. -/
@[inline] def map (f : α → β) (v : Vector α n) : Vector β n :=
  ⟨v.toArray.map f, by simp⟩

/-- Maps corresponding elements of two vectors of equal size using the function `f`. -/
@[inline] def zipWith (a : Vector α n) (b : Vector β n) (f : α → β → φ) : Vector φ n :=
  ⟨Array.zipWith a.toArray b.toArray f, by simp⟩

/-- The vector of length `n` whose `i`-th element is `f i`. -/
@[inline] def ofFn (f : Fin n → α) : Vector α n :=
  ⟨Array.ofFn f, by simp⟩

/--
Swap two elements of a vector using `Fin` indices.

This will perform the update destructively provided that the vector has a reference count of 1.
-/
@[inline] def swap (v : Vector α n) (i j : Fin n) : Vector α n :=
  ⟨v.toArray.swap (Fin.cast v.size_toArray.symm i) (Fin.cast v.size_toArray.symm j), by simp⟩

/--
Swap two elements of a vector using `Nat` indices. By default, the `get_elem_tactic` is used to
synthesize proofs that the indices are within bounds.

This will perform the update destructively provided that the vector has a reference count of 1.
-/
@[inline] def swapN (v : Vector α n) (i j : Nat)
    (hi : i < n := by get_elem_tactic) (hj : j < n := by get_elem_tactic) : Vector α n :=
  ⟨v.toArray.swapN i j (by simp_all) (by simp_all), by simp⟩

/--
Swap two elements of a vector using `Nat` indices. Panics if either index is out of bounds.

This will perform the update destructively provided that the vector has a reference count of 1.
-/
@[inline] def swap! (v : Vector α n) (i j : Nat) : Vector α n :=
  ⟨v.toArray.swap! i j, by simp⟩

/--
Swaps an element of a vector with a given value using a `Fin` index. The original value is returned
along with the updated vector.

This will perform the update destructively provided that the vector has a reference count of 1.
-/
@[inline] def swapAt (v : Vector α n) (i : Fin n) (x : α) : α × Vector α n :=
  let a := v.toArray.swapAt (Fin.cast v.size_toArray.symm i) x
  ⟨a.fst, a.snd, by simp [a]⟩

/--
Swaps an element of a vector with a given value using a `Nat` index. By default, the
`get_elem_tactic` is used to synthesise a proof that the index is within bounds. The original value
is returned along with the updated vector.

This will perform the update destructively provided that the vector has a reference count of 1.
-/
@[inline] def swapAtN (v : Vector α n) (i : Nat) (x : α) (h : i < n := by get_elem_tactic) :
    α × Vector α n :=
  let a := v.toArray.swapAtN i x (by simp_all)
  ⟨a.fst, a.snd, by simp [a]⟩

/--
Swaps an element of a vector with a given value using a `Nat` index. Panics if the index is out of
bounds. The original value is returned along with the updated vector.

This will perform the update destructively provided that the vector has a reference count of 1.
-/
@[inline] def swapAt! (v : Vector α n) (i : Nat) (x : α) : α × Vector α n :=
  let a := v.toArray.swapAt! i x
  ⟨a.fst, a.snd, by simp [a]⟩

/-- The vector `#v[0,1,2,...,n-1]`. -/
@[inline] def range (n : Nat) : Vector Nat n := ⟨Array.range n, by simp⟩

/--
Extract the first `m` elements of a vector. If `m` is greater than or equal to the size of the
vector then the vector is returned unchanged.
-/
@[inline] def take (v : Vector α n) (m : Nat) : Vector α (min m n) :=
  ⟨v.toArray.take m, by simp⟩

@[deprecated (since := "2024-10-22")] alias shrink := take

@[deprecated (since := "2024-11-20")] alias eraseIdxN := eraseIdx

/-- Use `#v[]` instead. -/
@[deprecated "Use `#v[]`." (since := "2024-11-27")]
def empty (α : Type u) : Vector α 0 := #v[]

proof_wanted instLawfulBEq (α n) [BEq α] [LawfulBEq α] : LawfulBEq (Vector α n)

/--
Returns `true` when all elements of the vector are pairwise distinct using `==` for comparison.
-/
@[inline] def allDiff [BEq α] (as : Vector α n) : Bool :=
  as.toArray.allDiff

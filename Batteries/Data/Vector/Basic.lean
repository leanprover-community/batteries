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

namespace Batteries

/-- `Vector α n` is an `Array α` with size `n`. -/
structure Vector (α : Type u) (n : Nat) extends Array α where
  /-- Array size. -/
  size_toArray : toArray.size = n
deriving Repr, DecidableEq

attribute [simp] Vector.size_toArray

namespace Vector

@[deprecated (since := "2024-10-15")] alias size_eq := size_toArray

/-- Syntax for `Vector α n` -/
syntax "#v[" withoutPosition(sepBy(term, ", ")) "]" : term

open Lean in
macro_rules
  | `(#v[ $elems,* ]) => `(Vector.mk (n := $(quote elems.getElems.size)) #[$elems,*] rfl)

/-- Custom eliminator for `Vector α n` through `Array α` -/
@[elab_as_elim]
def elimAsArray {motive : Vector α n → Sort u}
    (mk : ∀ (a : Array α) (ha : a.size = n), motive ⟨a, ha⟩) :
    (v : Vector α n) → motive v
  | ⟨a, ha⟩ => mk a ha

/-- Custom eliminator for `Vector α n` through `List α` -/
@[elab_as_elim]
def elimAsList {motive : Vector α n → Sort u}
    (mk : ∀ (a : List α) (ha : a.length = n), motive ⟨⟨a⟩, ha⟩) :
    (v : Vector α n) → motive v
  | ⟨⟨a⟩, ha⟩ => mk a ha

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
  v.toArray.get (i.cast v.size_toArray.symm)

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

/--
Deletes the first `m` elements of a vector. If `m` is greater than or equal to the size of the
vector then the empty vector is returned.
-/
@[inline] def drop (v : Vector α n) (m : Nat) : Vector α (n - m) :=
  ⟨v.toArray.extract m v.size, by simp⟩

/--
Compares two vectors of the same size using a given boolean relation `r`. `isEqv v w r` returns
`true` if and only if `r v[i] w[i]` is true for all indices `i`.
-/
@[inline] def isEqv (v w : Vector α n) (r : α → α → Bool) : Bool :=
  Array.isEqvAux v.toArray w.toArray (by simp) r n (by simp)

instance [BEq α] : BEq (Vector α n) where
  beq a b := isEqv a b (· == ·)

proof_wanted instLawfulBEq (α n) [BEq α] [LawfulBEq α] : LawfulBEq (Vector α n)

/-- Reverse the elements of a vector. -/
@[inline] def reverse (v : Vector α n) : Vector α n :=
  ⟨v.toArray.reverse, by simp⟩

/-- Delete an element of a vector using a `Fin` index. -/
@[inline] def feraseIdx (v : Vector α n) (i : Fin n) : Vector α (n-1) :=
  ⟨v.toArray.feraseIdx (Fin.cast v.size_toArray.symm i), by simp [Array.size_feraseIdx]⟩

/-- Delete an element of a vector using a `Nat` index. Panics if the index is out of bounds. -/
@[inline] def eraseIdx! (v : Vector α n) (i : Nat) : Vector α (n-1) :=
  if _ : i < n then
    ⟨v.toArray.eraseIdx i, by simp [*]⟩
  else
    have : Inhabited (Vector α (n-1)) := ⟨v.pop⟩
    panic! "index out of bounds"

/-- Delete the first element of a vector. Returns the empty vector if the input vector is empty. -/
@[inline] def tail (v : Vector α n) : Vector α (n-1) :=
  if _ : 0 < n then
    ⟨v.toArray.eraseIdx 0, by simp [*]⟩
  else
    v.cast (by omega)

/--
Delete an element of a vector using a `Nat` index. By default, the `get_elem_tactic` is used to
synthesise a proof that the index is within bounds.
-/
@[inline] def eraseIdxN (v : Vector α n) (i : Nat) (h : i < n := by get_elem_tactic) :
  Vector α (n - 1) := ⟨v.toArray.eraseIdxN i (by simp [*]), by simp⟩

/--
Finds the first index of a given value in a vector using `==` for comparison. Returns `none` if the
no element of the index matches the given value.
-/
@[inline] def indexOf? [BEq α] (v : Vector α n) (x : α) : Option (Fin n) :=
  (v.toArray.indexOf? x).map (Fin.cast v.size_toArray)

/-- Returns `true` when `v` is a prefix of the vector `w`. -/
@[inline] def isPrefixOf [BEq α] (v : Vector α m) (w : Vector α n) : Bool :=
  v.toArray.isPrefixOf w.toArray

/--
Returns `true` when all elements of the vector are pairwise distinct using `==` for comparison.
-/
@[inline] def allDiff [BEq α] (as : Vector α n) : Bool :=
  as.toArray.allDiff

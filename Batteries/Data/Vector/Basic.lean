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

@[deprecated (since := "2024-11-24")] alias swapAtN := swapAt

@[deprecated (since := "2024-10-22")] alias shrink := take

@[deprecated (since := "2024-11-20")] alias eraseIdxN := eraseIdx

<<<<<<< HEAD
/-- Use `#v[]` instead. -/
@[deprecated "Use `#v[]`." (since := "2024-11-27")]
def empty (α : Type u) : Vector α 0 := #v[]
=======
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

/-- Delete an element of a vector using a `Nat` index and a tactic provided proof. -/
@[inline] def eraseIdx (v : Vector α n) (i : Nat) (h : i < n := by get_elem_tactic) :
    Vector α (n-1) :=
  ⟨v.toArray.eraseIdx i (v.size_toArray.symm ▸ h), by simp [Array.size_eraseIdx]⟩

/-- Delete an element of a vector using a `Nat` index. Panics if the index is out of bounds. -/
@[inline] def eraseIdx! (v : Vector α n) (i : Nat) : Vector α (n-1) :=
  if _ : i < n then
    v.eraseIdx i
  else
    have : Inhabited (Vector α (n-1)) := ⟨v.pop⟩
    panic! "index out of bounds"

/-- Delete the first element of a vector. Returns the empty vector if the input vector is empty. -/
@[inline] def tail (v : Vector α n) : Vector α (n-1) :=
  if _ : 0 < n then
    v.eraseIdx 0
  else
    v.cast (by omega)

@[deprecated (since := "2024-11-20")] alias eraseIdxN := eraseIdx

/--
Finds the first index of a given value in a vector using `==` for comparison. Returns `none` if the
no element of the index matches the given value.
-/
@[inline] def indexOf? [BEq α] (v : Vector α n) (x : α) : Option (Fin n) :=
  (v.toArray.indexOf? x).map (Fin.cast v.size_toArray)

/-- Returns `true` when `v` is a prefix of the vector `w`. -/
@[inline] def isPrefixOf [BEq α] (v : Vector α m) (w : Vector α n) : Bool :=
  v.toArray.isPrefixOf w.toArray
>>>>>>> bump/v4.15.0

/--
Returns `true` when all elements of the vector are pairwise distinct using `==` for comparison.
-/
@[inline] def allDiff [BEq α] (as : Vector α n) : Bool :=
  as.toArray.allDiff

/-
Copyright (c) 2024 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas, Francois Dorais
-/

import Batteries.Data.Vector.Basic
import Batteries.Data.List.Basic
import Batteries.Data.List.Lemmas
import Batteries.Data.Array.Lemmas

/-!
## Vectors
Lemmas about `Vector α n`
-/

namespace Batteries

namespace Vector


/-- An `empty` vector maps to a `empty` vector. -/
@[simp]
theorem map_empty (f : α → β) : map f empty = empty := by
  rw [map, empty, mk.injEq]
  exact Array.map_empty f

theorem toArray_injective : ∀ {v w : Vector α n}, v.toArray = w.toArray → v = w
  | {..}, {..}, rfl => rfl

/-- A vector of length `0` is an `empty` vector. -/
protected theorem eq_empty (v : Vector α 0) : v = empty := by
  apply Vector.toArray_injective
  apply Array.eq_empty_of_size_eq_zero v.2

/--
`Vector.ext` is an extensionality theorem.
Vectors `a` and `b` are equal to each other if their elements are equal for each valid index.
-/
@[ext]
protected theorem ext {a b : Vector α n} (h : (i : Nat) → (_ : i < n) → a[i] = b[i]) : a = b := by
  apply Vector.toArray_injective
  apply Array.ext
  · rw [a.size_eq, b.size_eq]
  · intro i hi _
    rw [a.size_eq] at hi
    exact h i hi

@[simp] theorem getElem_mk (data : Array α) (size : data.size = n) (i : Nat) (h : i < n) :
    (Vector.mk data size)[i] = data[i] := rfl

@[simp] theorem push_mk (data : Array α) (size : data.size = n) (x : α) :
    (Vector.mk data size).push x =
      Vector.mk (data.push x) (by simp [size, Nat.succ_eq_add_one]) := rfl

@[simp] theorem pop_mk (data : Array α) (size : data.size = n) :
    (Vector.mk data size).pop = Vector.mk data.pop (by simp [size]) := rfl

@[simp] theorem getElem_push_last (v : Vector α n) (x : α) : (v.push x)[n] = x := by
  rcases v with ⟨data, rfl⟩
  simp

@[simp] theorem getElem_push_lt (v : Vector α n) (x : α) (i : Nat) (h : i < n) :
    (v.push x)[i] = v[i] := by
  rcases v with ⟨data, rfl⟩
  simp [Array.get_push_lt, h] -- should be a simp lemma?

@[simp] theorem getElem_pop (v : Vector α n) (i : Nat) (h : i < n - 1) : (v.pop)[i] = v[i] := by
  rcases v with ⟨data, rfl⟩
  simp

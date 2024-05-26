/-
Copyright (c) 2024 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas, Francois Dorais
-/

import Batteries.Data.Vector.Basic
import Batteries.Data.List.Basic
import Batteries.Data.List.Lemmas

/-!
## Vectors
Lemmas about `Vector α n`
-/

namespace Batteries

namespace Vector

/-- An `empty` vector maps to a `empty` vector. -/
@[simp]
theorem map_empty (f : α → β) : map f empty = empty :=
  rfl


theorem eq : ∀ v w : Vector α n, v.toArray = w.toArray → v = w
  | {..}, {..}, rfl => rfl

/-- A vector of length `0` is an `empty` vector. -/
protected theorem eq_empty (v : Vector α 0) : v = empty := by
  apply Vector.eq v #v[]
  apply Array.eq_empty_of_size_eq_zero v.2

/--
`Vector.ext` is an extensionality theorem.
Vectors `a` and `b` are equal to each other if their elements are equal for each valid index.
-/
@[ext]
protected theorem ext (a b : Vector α n) (h : (i : Nat) → (_ : i < n) → a[i] = b[i]) : a = b := by
  apply Vector.eq
  apply Array.ext
  · rw [a.size_eq, b.size_eq]
  · intro i hi _
    rw [a.size_eq] at hi
    exact h i hi

end Vector

end Batteries

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

/-- Use `#v[]` instead. -/
@[deprecated "Use `#v[]`." (since := "2024-11-27")]
def empty (α : Type u) : Vector α 0 := #v[]

proof_wanted instLawfulBEq (α n) [BEq α] [LawfulBEq α] : LawfulBEq (Vector α n)

/--
Returns `true` when all elements of the vector are pairwise distinct using `==` for comparison.
-/
@[inline] def allDiff [BEq α] (as : Vector α n) : Bool :=
  as.toArray.allDiff

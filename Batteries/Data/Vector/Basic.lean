/-
Copyright (c) 2024 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas, François G. Dorais
-/


/-!
# Vectors

`Vector α n` is a thin wrapper around `Array α` for arrays of fixed size `n`.
-/

namespace Vector

/--
Returns `true` when all elements of the vector are pairwise distinct using `==` for comparison.
-/
@[inline] def allDiff [BEq α] (as : Vector α n) : Bool :=
  as.toArray.allDiff

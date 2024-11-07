/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import Batteries.Data.Vector.Basic
import Batteries.Data.Array.Monadic

namespace Batteries.Vector

/-- Map a monadic function over a vector. -/
def mapM [Monad m] (f : α → m β) (v : Vector α n) : m (Vector β n) := do
  go 0 (Nat.zero_le n) .empty
where
  go (i : Nat) (h : i ≤ n) (r : Vector β i) : m (Vector β n) := do
    if h' : i < n then
      go (i+1) (by omega) (r.push (← f v[i]))
    else
      return r.cast (by omega)

end Batteries.Vector

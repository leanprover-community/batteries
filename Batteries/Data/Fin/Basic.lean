/-
Copyright (c) 2017 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis, Keeley Hoek, Mario Carneiro
-/
import Batteries.Data.Array.Basic
import Batteries.Data.List.Basic
import Batteries.Tactic.Alias

namespace Fin

/-- `min n m` as an element of `Fin (m + 1)` -/
def clamp (n m : Nat) : Fin (m + 1) := ⟨min n m, Nat.lt_succ_of_le (Nat.min_le_right ..)⟩

/-- `enum n` is the array of all elements of `Fin n` in order -/
@[deprecated (since:="2024-07-30")] alias enum := Array.finRange

/-- `list n` is the list of all elements of `Fin n` in order -/
@[deprecated (since:="2024-07-30")] alias list := List.finRange

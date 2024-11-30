/-
Copyright (c) 2017 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis, Keeley Hoek, Mario Carneiro
-/
import Batteries.Tactic.Alias
import Batteries.Data.Array.Basic
import Batteries.Data.List.Basic

namespace Fin

/-- `min n m` as an element of `Fin (m + 1)` -/
def clamp (n m : Nat) : Fin (m + 1) := ⟨min n m, Nat.lt_succ_of_le (Nat.min_le_right ..)⟩

@[deprecated (since := "2024-11-15")]
alias enum := Array.finRange

@[deprecated (since := "2024-11-15")]
alias list := List.finRange

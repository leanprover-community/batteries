/-
Copyright (c) 2014 Parikshit Khanna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Parikshit Khanna, Jeremy Avigad, Leonardo de Moura, Floris van Doorn, Mario Carneiro
-/
import Std.Classes.SetNotation

namespace List

open Nat

/-!
# Bootstrapping theorems for lists

These are theorems used in the definitions of `Std.Data.List.Basic` and tactics.
New theorems should be added to `Std.Data.List.Lemmas` if they are not needed by the bootstrap.
-/

theorem filter_eq_nil {l} : filter p l = [] ↔ ∀ a, a ∈ l → ¬p a := by
  simp only [eq_nil_iff_forall_not_mem, mem_filter, not_and]

-- A specialization of `minimum?_eq_some_iff` to Nat.
theorem minimum?_eq_some_iff' {xs : List Nat} :
    xs.minimum? = some a ↔ (a ∈ xs ∧ ∀ b ∈ xs, a ≤ b) :=
  minimum?_eq_some_iff
    (le_refl := Nat.le_refl)
    (min_eq_or := fun _ _ => Nat.min_def .. ▸ by split <;> simp)
    (le_min_iff := fun _ _ _ => Nat.le_min)

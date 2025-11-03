/-
Copyright (c) 2024 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Kim Morrison
-/
module

@[expose] public section

/-!
While this file is currently empty, it is intended as a home for any lemmas which are required for
definitions in `Batteries.Data.Array.Basic`, but which are not provided by Lean.
-/

/-! ### push -/
theorem Array.push_push_eq_append {as : Array α} {a b : α} :
    (as.push a).push b = as ++ #[a, b] := rfl

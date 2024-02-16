/-
Copyright (c) 2023 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/

import Std.Tactic.Alias

/-!
# Specializations of basic logic lemmas

These are useful for `omega` while constructing proofs, but not considered generally useful
so are hidden in the `Std.Tactic.Omega` namespace.

If you find yourself needing them elsewhere, please move them first to another file.
-/

namespace Std.Tactic.Omega

alias ⟨and_not_not_of_not_or, _⟩ := not_or
alias ⟨Decidable.or_not_not_of_not_and, _⟩ := Decidable.not_and_iff_or_not

alias ⟨Decidable.and_or_not_and_not_of_iff, _⟩ := Decidable.iff_iff_and_or_not_and_not

theorem Decidable.not_iff_iff_and_not_or_not_and [Decidable a] [Decidable b] :
    (¬ (a ↔ b)) ↔ (a ∧ ¬ b) ∨ ((¬ a) ∧ b) := by
  by_cases b <;> simp_all [Decidable.not_not]

alias ⟨Decidable.and_not_or_not_and_of_not_iff, _⟩ := Decidable.not_iff_iff_and_not_or_not_and

alias ⟨Decidable.and_not_of_not_imp, _⟩ := Decidable.not_imp_iff_and_not

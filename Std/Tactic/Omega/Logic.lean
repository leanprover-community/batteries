/-
Copyright (c) 2023 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/

import Std.Tactic.Alias
import Std.Logic

/-!
# Specializations of basic logic lemmas

These are useful for `omega` while constructing proofs, but not considered generally useful
so are hidden in the `Std.Tactic.Omega` namespace.

If you find yourself needing them elsewhere, please move them first to `Std.Logic`.
-/

namespace Std.Tactic.Omega

alias ⟨and_not_not_of_not_or, _⟩ := not_or
alias ⟨Decidable.or_not_not_of_not_and, _⟩ := Decidable.not_and_iff_or_not

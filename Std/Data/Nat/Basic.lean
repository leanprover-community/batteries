/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad, Mario Carneiro
-/
import Std.Classes.Dvd

namespace Nat

/--
Divisibility of natural numbers. `a ∣ b` (typed as `\|`) says that
there is some `c` such that `b = a * c`.
-/
instance : Dvd Nat := ⟨fun a b => ∃ c, b = a * c⟩

/-- Sum of a list of natural numbers. -/
protected def sum (l : List Nat) : Nat := l.foldr (·+·) 0

/-
Copyright (c) 2022 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/

/-- Notation typeclass for the `∣` operation (typed as `\|`), which represents divisibility. -/
class Dvd (α : Type _) where
  /-- Divisibility. `a ∣ b` (typed as `\|`) means that there is some `c` such that `b = a * c`. -/
  dvd : α → α → Prop

@[inheritDoc] infix:50 " ∣ " => Dvd.dvd

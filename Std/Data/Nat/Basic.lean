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
instance : Dvd Nat where dvd := divides

/-- Sum of a list of natural numbers. -/
protected def sum (l : List Nat) : Nat := l.foldr (·+·) 0

/--
Integer square root function. Implemented via Newton's method.
-/
def sqrt (n : Nat) : Nat :=
  if n ≤ 1 then n else
  iter n (n / 2)
where
  /-- Auxiliary for `sqrt`. If `guess` is greater than the integer square root of `n`,
  returns the integer square root of `n`. -/
  iter (n guess : Nat) : Nat :=
    let next := (guess + n / guess) / 2
    if _h : next < guess then
      iter n next
    else
      guess
termination_by iter guess => guess

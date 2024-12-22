/-
Copyright (c) 2022 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Batteries.Data.Rat.Basic
import Batteries.Lean.Float

/-! # Rational Numbers and Float -/

namespace Rat

/-- Convert this rational number to a `Float` value. -/
protected def toFloat (a : Rat) : Float := a.num.divFloat a.den

/-- Convert this floating point number to a rational value. -/
protected def _root_.Float.toRat? (a : Float) : Option Rat :=
  a.toRatParts.map fun (v, exp) =>
    mkRat (v.sign * v.natAbs <<< exp.toNat) (1 <<< (-exp).toNat)

/--
Convert this floating point number to a rational value,
mapping non-finite values (`inf`, `-inf`, `nan`) to 0.
-/
protected def _root_.Float.toRat0 (a : Float) : Rat := a.toRat?.getD 0

instance : Coe Rat Float := ⟨Rat.toFloat⟩

end Rat

/-
 Copyright (c) 2022 E.W.Ayers. All rights reserved.
 Released under Apache 2.0 license as described in the file LICENSE.
 Authors: E.W.Ayers, Mario Carneiro
-/
import Lean.Data.Json.FromToJson
import Batteries.Lean.Float

open Lean

instance : OfScientific JsonNumber where
  ofScientific mantissa exponentSign decimalExponent :=
    if exponentSign then
      { mantissa := mantissa, exponent := decimalExponent }
    else
      { mantissa := (mantissa * 10 ^ decimalExponent : Nat), exponent := 0 }

instance : Neg JsonNumber where
  neg jn := ⟨-jn.mantissa, jn.exponent⟩

instance : ToJson Float where
  toJson x :=
    match x.toRatParts' with
    | none => Json.null
    | some (n, d) =>
      if d < 0 then
        Json.num { mantissa := n * (5^d.natAbs : Nat), exponent := d.natAbs }
      else
        Json.num { mantissa := n * (2^d.natAbs : Nat), exponent := 0 }

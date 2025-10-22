/-
Copyright (c) 2025 Robin Arnez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Arnez
-/

import Batteries.Data.Nat.Basic

/-!
# Simple functions used in the axiomatic redefinition of floats (temporary).
-/

/-- Returns whether `x` is a NaN bit pattern, that is: `Float.ofBits x = Float.nan` -/
def Float.isNaNBits (x : UInt64) : Bool :=
  (x >>> 52) &&& 0x7ff = 0x7ff ∧ x &&& 0x000f_ffff_ffff_ffff ≠ 0

/--
Returns the sign bit of the given floating point number, i.e. whether
the given `Float` is negative. NaN is considered positive in this function.
-/
def Float.signBit (x : Float) : Bool :=
  x.toBits >>> 63 ≠ 0

/--
Returns the exponent part of the given floating point number which is a value between
`0` and `2047` (inclusive) describing the exponent of the floating point number.
NaN and infinity have exponent part `2047`, `1` has exponent part `1023`, `2` has `1024`, etc.
-/
def Float.exponentPart (x : Float) : UInt64 :=
  (x.toBits >>> 52) &&& 0x7ff

/--
Returns the mantissa of the given floating point number (without any implicit digits).
-/
def Float.mantissa (x : Float) : UInt64 :=
  x.toBits &&& 0x000f_ffff_ffff_ffff

/--
Constructs a floating point number from the given parts (sign, exponent and mantissa).
This function expects `exponentPart < 2047` and `mantissa < 2 ^ 52` in order to work correctly.
-/
def Float.fromParts (exponentPart : UInt64) (mantissa : UInt64) : Float :=
  Float.ofBits ((exponentPart <<< 52) ||| mantissa)

/--
The floating point value "positive infinity", also used to represent numerical computations
which produce finite values outside of the representable range of `Float`.
-/
def Float.inf : Float := fromParts 2047 0

/--
The floating point value "not a number", used to represent erroneous numerical computations
such as `0 / 0`. Using `nan` in any float operation will return `nan`, and all comparisons
involving `nan` except `!=` return `false`, including in particular `nan == nan`.
-/
def Float.nan : Float := fromParts 2047 0x0008_0000_0000_0000

/--
Returns a pair of values `(a, b)` such `x = a / b` (assuming `x` is finite).
-/
def Float.toNumDenPair (x : Float) : Int × Nat :=
  let signMul := bif x.signBit then (-1) else 1
  let exp := x.exponentPart
  if exp = 0 then (x.mantissa.toNat * signMul, 1 <<< 1074)
  else
    let mant := x.mantissa.toNat ||| 0x0010_0000_0000_0000
    (mant <<< (exp.toNat - 1075) * signMul, 1 <<< (1075 - exp.toNat))

/--
Divide two natural numbers, to produce a correctly rounded (nearest-ties-to-even) `Float` result.
-/
def Nat.divFloat (x y : Nat) : Float :=
  if y = 0 then if x = 0 then Float.nan else Float.inf else
  if x = 0 then Float.fromParts 0 0 else
  -- calculate `log2 = ⌊log 2 (x / y)⌋`
  let log2 : Int := x.log2 - y.log2
  let log2 := if x <<< y.log2 < y <<< x.log2 then log2 - 1 else log2
  -- if `x / y ≥ 2 ^ 1024`, return positive infinity
  if log2 ≥ 1024 then Float.inf else

  let exp := 53 - max log2 (-1022)
  -- calculate `mantissa = round (x / y * 2 ^ (exp - 1))` (rounding nearest-ties-to-even)
  let num := x <<< exp.toNat
  let den := y <<< (-exp).toNat
  let div := num / den
  let mantissa :=
    if div &&& 3 = 1 ∧ div * den = num then div >>> 1 else (div + 1) >>> 1

  if log2 < -1022 then
    -- subnormal
    if mantissa = 0x0010_0000_0000_0000 then -- overflow
      Float.fromParts 1 0 -- smallest normal float
    else
      Float.fromParts 0 mantissa.toUInt64
  else
    -- normal
    if mantissa = 0x0020_0000_0000_0000 then -- overflow
      -- also works for infinity
      Float.fromParts (log2 + 1024).natAbs.toUInt64 0
    else
      Float.fromParts (log2 + 1023).natAbs.toUInt64
        (mantissa.toUInt64 &&& 0x000f_ffff_ffff_ffff)

/--
Returns `sqrt (x * 2 ^ e)` as a floating point number.
-/
def Float.sqrtHelper (x : Nat) (e : Int) : Float :=
  -- log 2 (sqrt (x * 2 ^ e)) = log 2 (x * 2 ^ e) / 2 = ((log 2 x) + e) / 2
  let log2 := (x.log2 + e) >>> 1
  if log2 ≥ 1024 then Float.inf else

  -- we want `mantissa = round (sqrt (x * 2 ^ e) * 2 ^ exp)`
  -- round (sqrt (x * 2 ^ e) * 2 ^ exp) =
  -- round (sqrt (x * 2 ^ (e + 2 * exp)))
  -- we want variables `expInner` and `expOuter` with
  -- sqrt (x * 2 ^ (e + 2 * exp)) = sqrt (x * 2 ^ expInner) >>> expOuter
  -- TODO: prove that this implementation actually works
  let exp := 53 - max log2 (-1022)
  let e := e + 2 * exp
  let expInner := if e < 0 then (-e).toNat &&& 1 else e.toNat
  let expOuter := if e < 0 then (-e).toNat >>> 1 else 0
  let val := x <<< expInner
  let sqrt := val.sqrt
  let result := sqrt >>> expOuter -- result = ⌊sqrt (x * 2 ^ e) * 2 ^ exp * 2⌋
  let mantissa :=
    if result &&& 3 = 1 ∧ result * result = val then result >>> 1 else (result + 1) >>> 1

  if log2 < -1022 then
    -- subnormal
    if mantissa = 0x0010_0000_0000_0000 then -- overflow
      Float.fromParts 1 0 -- smallest normal float
    else
      Float.fromParts 0 mantissa.toUInt64
  else
    -- normal
    if mantissa = 0x0020_0000_0000_0000 then -- overflow
      -- also works for infinity
      Float.fromParts (log2 + 1024).natAbs.toUInt64 0
    else
      Float.fromParts (log2 + 1023).natAbs.toUInt64
        (mantissa.toUInt64 &&& 0x000f_ffff_ffff_ffff)

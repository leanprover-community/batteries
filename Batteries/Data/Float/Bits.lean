/-
 Copyright (c) 2026 François G. Dorais. All rights reserved.
 Released under Apache 2.0 license as described in the file LICENSE.
 Authors: François G. Dorais
-/
module

/-!
# Bit-level utilities for `Float` and `Float32`

Classification, sign manipulation and neighbor functions from IEEE 754-2019 §5.3.1, §5.5.1 and
§5.7.2, together with unit in the last place and distance in units in the last place.

All functions are defined in terms of `toBits` and `ofBits` and check for `NaN` first. The logical
model of Lean's floats has a single canonical `NaN`, while compiled code may see any `NaN` bit
pattern, so this keeps the compiled behavior in line with the model. As a consequence, `NaN` has
no sign here: `signBit nan = false`, and `copySign x nan` is `x` with a positive sign.
-/

/-- The class of a floating-point number, following IEEE 754-2019 §5.7.2. -/
public inductive Float.Category where
  /-- Not a number. -/
  | nan
  /-- Positive or negative infinity. -/
  | infinite
  /-- Positive or negative zero. -/
  | zero
  /-- A nonzero number whose exponent field is zero. -/
  | subnormal
  /-- A finite number whose exponent field is not zero. -/
  | normal
deriving DecidableEq, Repr, Inhabited

namespace Float

/-- The sign bit of a `Float`. -/
@[expose] public def signMask : UInt64 := 0x8000000000000000

/-- The exponent field of a `Float`. -/
@[expose] public def exponentMask : UInt64 := 0x7FF0000000000000

/-- The significand field of a `Float`. -/
@[expose] public def significandMask : UInt64 := 0x000FFFFFFFFFFFFF

/-- The class of `x`, as in IEEE 754-2019 §5.7.2. -/
@[expose] public def classify (x : Float) : Category :=
  if x.isNaN then .nan else
    let e := x.toBits &&& exponentMask
    if e == exponentMask then .infinite
    else if e == 0 then
      if x.toBits &&& significandMask == 0 then .zero else .subnormal
    else .normal

/-- Whether `x` is a normal number: finite, nonzero and not subnormal. -/
@[expose] public def isNormal (x : Float) : Bool := x.classify == .normal

/-- Whether `x` is a subnormal number. -/
@[expose] public def isSubnormal (x : Float) : Bool := x.classify == .subnormal

/--
Whether the sign bit of `x` is set, as in IEEE 754-2019 §5.7.2 `isSignMinus`.

This is `true` for `-0` and `false` for `NaN`, since Lean's floats have a single `NaN` value.
-/
@[expose] public def signBit (x : Float) : Bool :=
  !x.isNaN && x.toBits &&& signMask != 0

/--
The value `x` with the sign of `y`, as in IEEE 754-2019 §5.5.1.

`NaN` inputs follow `signBit`: `copySign nan y = nan` and `copySign x nan` has a positive sign.
-/
@[expose] public def copySign (x y : Float) : Float :=
  if x.isNaN then x else
    ofBits (x.toBits &&& ~~~signMask ||| if y.signBit then signMask else 0)

/--
The least floating-point number that compares greater than `x`, as in IEEE 754-2019 §5.3.1.

Special cases: `nextUp nan = nan`, `nextUp inf = inf`, `nextUp (-inf)` is the most negative
finite number, and `nextUp` of either zero is the smallest positive subnormal number.
-/
@[expose] public def nextUp (x : Float) : Float :=
  if x.isNaN then x else
    let b := x.toBits
    if b &&& ~~~signMask == 0 then ofBits 1
    else if b &&& signMask != 0 then ofBits (b - 1)
    else if b == exponentMask then x
    else ofBits (b + 1)

/--
The greatest floating-point number that compares less than `x`, as in IEEE 754-2019 §5.3.1.

This is `-nextUp (-x)`.
-/
@[expose] public def nextDown (x : Float) : Float := -nextUp (-x)

/--
The unit in the last place of `x`: the distance from `|x|` to the next number of larger
magnitude. For the largest finite number, it is the distance to the next number of smaller
magnitude. This agrees with Julia's `eps(x)`.

Special cases: `ulp 0` is the smallest positive subnormal number, and `ulp x = nan` when `x` is
infinite or `NaN`.
-/
@[expose] public def ulp (x : Float) : Float :=
  if x.isNaN then x else
    let b := x.toBits &&& ~~~signMask
    if b == exponentMask then nan
    else if b + 1 == exponentMask then ofBits b - ofBits (b - 1)
    else ofBits (b + 1) - ofBits b

/--
The position of `x` on the number line that counts floating-point numbers, with both zeros at
`0`, positive numbers at their bit pattern and negative numbers at the negation of the bit
pattern of their absolute value. Infinities sit one step past the largest finite numbers.
`x` must not be `NaN`; see also `toOrdinal?` and `toOrdinal!`.
-/
@[expose] public def toOrdinal (x : Float) (_ : x.isNaN = false) : Int :=
  let m := (x.toBits &&& ~~~signMask).toNat
  if x.toBits &&& signMask != 0 then -m else m

/-- The position of `x` on the number line that counts floating-point numbers, as in
`toOrdinal`, or `none` when `x` is `NaN`. -/
@[expose] public def toOrdinal? (x : Float) : Option Int :=
  if h : x.isNaN = false then some (x.toOrdinal h) else none

/-- The position of `x` on the number line that counts floating-point numbers, as in
`toOrdinal`. Panics when `x` is `NaN`. -/
@[expose] public def toOrdinal! (x : Float) : Int :=
  if h : x.isNaN = false then x.toOrdinal h else panic! "toOrdinal!: NaN argument"

/--
The number of floating-point numbers between `x` and `y`, counting one of the endpoints: the
distance between them in units in the last place. Both zeros count as the same point and the
infinities are one step beyond the largest finite numbers. Neither argument may be `NaN`; see
also `ulpDistance?` and `ulpDistance!`.
-/
@[expose] public def ulpDistance (x y : Float) (hx : x.isNaN = false) (hy : y.isNaN = false) :
    Nat :=
  (x.toOrdinal hx - y.toOrdinal hy).natAbs

/-- The distance between `x` and `y` in units in the last place, as in `ulpDistance`, or
`none` when either argument is `NaN`. -/
@[expose] public def ulpDistance? (x y : Float) : Option Nat :=
  if h : x.isNaN = false ∧ y.isNaN = false then some (ulpDistance x y h.1 h.2) else none

/-- The distance between `x` and `y` in units in the last place, as in `ulpDistance`.
Panics when either argument is `NaN`. -/
@[expose] public def ulpDistance! (x y : Float) : Nat :=
  if h : x.isNaN = false ∧ y.isNaN = false then ulpDistance x y h.1 h.2
  else panic! "ulpDistance!: NaN argument"

public theorem toOrdinal?_eq_some {x : Float} (h : x.isNaN = false) :
    x.toOrdinal? = some (x.toOrdinal h) := by simp [toOrdinal?, h]

public theorem toOrdinal?_eq_none {x : Float} (h : x.isNaN = true) : x.toOrdinal? = none := by
  simp [toOrdinal?, h]

public theorem toOrdinal!_eq {x : Float} (h : x.isNaN = false) : x.toOrdinal! = x.toOrdinal h := by
  simp [toOrdinal!, h]

public theorem ulpDistance?_eq_some {x y : Float} (hx : x.isNaN = false) (hy : y.isNaN = false) :
    ulpDistance? x y = some (ulpDistance x y hx hy) := by simp [ulpDistance?, hx, hy]

public theorem ulpDistance?_eq_none {x y : Float} (h : x.isNaN = true ∨ y.isNaN = true) :
    ulpDistance? x y = none := by
  rcases h with h | h <;> simp [ulpDistance?, h]

public theorem ulpDistance!_eq {x y : Float} (hx : x.isNaN = false) (hy : y.isNaN = false) :
    ulpDistance! x y = ulpDistance x y hx hy := by simp [ulpDistance!, hx, hy]

end Float

namespace Float32

/-- The sign bit of a `Float32`. -/
@[expose] public def signMask : UInt32 := 0x80000000

/-- The exponent field of a `Float32`. -/
@[expose] public def exponentMask : UInt32 := 0x7F800000

/-- The significand field of a `Float32`. -/
@[expose] public def significandMask : UInt32 := 0x007FFFFF

@[inherit_doc Float.classify, expose] public def classify (x : Float32) : Float.Category :=
  if x.isNaN then .nan else
    let e := x.toBits &&& exponentMask
    if e == exponentMask then .infinite
    else if e == 0 then
      if x.toBits &&& significandMask == 0 then .zero else .subnormal
    else .normal

@[inherit_doc Float.isNormal, expose]
public def isNormal (x : Float32) : Bool := x.classify == .normal

@[inherit_doc Float.isSubnormal, expose]
public def isSubnormal (x : Float32) : Bool := x.classify == .subnormal

@[inherit_doc Float.signBit, expose] public def signBit (x : Float32) : Bool :=
  !x.isNaN && x.toBits &&& signMask != 0

@[inherit_doc Float.copySign, expose] public def copySign (x y : Float32) : Float32 :=
  if x.isNaN then x else
    ofBits (x.toBits &&& ~~~signMask ||| if y.signBit then signMask else 0)

@[inherit_doc Float.nextUp, expose] public def nextUp (x : Float32) : Float32 :=
  if x.isNaN then x else
    let b := x.toBits
    if b &&& ~~~signMask == 0 then ofBits 1
    else if b &&& signMask != 0 then ofBits (b - 1)
    else if b == exponentMask then x
    else ofBits (b + 1)

@[inherit_doc Float.nextDown, expose] public def nextDown (x : Float32) : Float32 := -nextUp (-x)

/--
The unit in the last place of `x`: the distance from `|x|` to the next number of larger
magnitude. For the largest finite number, it is the distance to the next number of smaller
magnitude. This agrees with Julia's `eps(x)`.

Special cases: `ulp 0` is the smallest positive subnormal number, and `ulp x = nan` when `x` is
infinite or `NaN`.
-/
@[expose] public def ulp (x : Float32) : Float32 :=
  if x.isNaN then x else
    let b := x.toBits &&& ~~~signMask
    if b == exponentMask then ofBits 0x7FC00000
    else if b + 1 == exponentMask then ofBits b - ofBits (b - 1)
    else ofBits (b + 1) - ofBits b

@[inherit_doc Float.toOrdinal, expose]
public def toOrdinal (x : Float32) (_ : x.isNaN = false) : Int :=
  let m := (x.toBits &&& ~~~signMask).toNat
  if x.toBits &&& signMask != 0 then -m else m

@[inherit_doc Float.toOrdinal?, expose] public def toOrdinal? (x : Float32) : Option Int :=
  if h : x.isNaN = false then some (x.toOrdinal h) else none

@[inherit_doc Float.toOrdinal!, expose] public def toOrdinal! (x : Float32) : Int :=
  if h : x.isNaN = false then x.toOrdinal h else panic! "toOrdinal!: NaN argument"

@[inherit_doc Float.ulpDistance, expose]
public def ulpDistance (x y : Float32) (hx : x.isNaN = false) (hy : y.isNaN = false) : Nat :=
  (x.toOrdinal hx - y.toOrdinal hy).natAbs

@[inherit_doc Float.ulpDistance?, expose] public def ulpDistance? (x y : Float32) : Option Nat :=
  if h : x.isNaN = false ∧ y.isNaN = false then some (ulpDistance x y h.1 h.2) else none

@[inherit_doc Float.ulpDistance!, expose] public def ulpDistance! (x y : Float32) : Nat :=
  if h : x.isNaN = false ∧ y.isNaN = false then ulpDistance x y h.1 h.2
  else panic! "ulpDistance!: NaN argument"

public theorem toOrdinal?_eq_some {x : Float32} (h : x.isNaN = false) :
    x.toOrdinal? = some (x.toOrdinal h) := by simp [toOrdinal?, h]

public theorem toOrdinal?_eq_none {x : Float32} (h : x.isNaN = true) : x.toOrdinal? = none := by
  simp [toOrdinal?, h]

public theorem toOrdinal!_eq {x : Float32} (h : x.isNaN = false) :
    x.toOrdinal! = x.toOrdinal h := by
  simp [toOrdinal!, h]

public theorem ulpDistance?_eq_some {x y : Float32} (hx : x.isNaN = false) (hy : y.isNaN = false) :
    ulpDistance? x y = some (ulpDistance x y hx hy) := by simp [ulpDistance?, hx, hy]

public theorem ulpDistance?_eq_none {x y : Float32} (h : x.isNaN = true ∨ y.isNaN = true) :
    ulpDistance? x y = none := by
  rcases h with h | h <;> simp [ulpDistance?, h]

public theorem ulpDistance!_eq {x y : Float32} (hx : x.isNaN = false) (hy : y.isNaN = false) :
    ulpDistance! x y = ulpDistance x y hx hy := by simp [ulpDistance!, hx, hy]

end Float32

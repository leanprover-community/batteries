/-
 Copyright (c) 2026 François G. Dorais. All rights reserved.
 Released under Apache 2.0 license as described in the file LICENSE.
 Authors: François G. Dorais
-/
module

public import Batteries.Data.Float.Bits

/-!
# Powers of two and scaling for `Float` and `Float32`

`twoPow n` is `2 ^ n` built from its bit pattern, `exponent? x` is the exponent of `x`
(`logB` of IEEE 754-2019 §5.3.3 on finite nonzero numbers), and `ldexp x n` is `x * 2 ^ n`
rounded once (`scaleB` of §5.3.3, and C's `ldexp` and `scalbn`).

Core's `Float.scaleB` and `Float.frExp` are opaque external functions. The functions here are
defined with bit casts and multiplication only, so they have a logical model and can be reasoned
about.

## References

* [IEEE754] *IEEE Standard for Floating-Point Arithmetic*, IEEE Std 754-2019.
* [musl] musl libc, `src/math/scalbn.c`.
-/

namespace Float

/--
`2 ^ n`, built from its bit pattern: exact for `-1074 ≤ n ≤ 1023`, `inf` above that range and
`0` below it.
-/
@[expose] public def twoPow (n : Int) : Float :=
  if n > 1023 then inf
  else if n ≥ -1022 then ofBits ((n + 1023).toNat.toUInt64 <<< 52)
  else if n ≥ -1074 then ofBits ((1 : UInt64) <<< (n + 1074).toNat.toUInt64)
  else 0

/--
The exponent of a finite nonzero `x`: the integer `e` with `2 ^ e ≤ |x| < 2 ^ (e + 1)`. This is
`logB` of [IEEE754, 5.3.3]. Subnormal numbers get their true exponent, from `-1074` to `-1023`.
-/
@[expose] public def exponent (x : Float) (_ : (x.isFinite && x != 0) = true) : Int :=
  let e := (x.toBits &&& exponentMask) >>> 52
  if e == 0 then ((x.toBits &&& significandMask).toNat.log2 : Int) - 1074
  else e.toNat - 1023

/-- The exponent of `x` (see `Float.exponent`), or `none` when `x` is zero, infinite or `NaN`. -/
@[expose] public def exponent? (x : Float) : Option Int :=
  if h : (x.isFinite && x != 0) = true then some (x.exponent h) else none

/-- The exponent of `x` (see `Float.exponent`). Panics when `x` is zero, infinite or `NaN`. -/
@[expose] public def exponent! (x : Float) : Int :=
  if h : (x.isFinite && x != 0) = true then x.exponent h
  else panic! "exponent!: zero, infinite or NaN argument"

/--
`x * 2 ^ n`, rounded once: `scaleB` of [IEEE754, 5.3.3] and the C functions `ldexp` and
`scalbn`. The steps are those of [musl]: when `n` is outside the range of `twoPow`, `x` is first
scaled by a power of two that cannot round, so that only the last multiplication rounds.
-/
@[expose] public def ldexp (x : Float) (n : Int) : Float :=
  if n > 1023 then
    let x := x * twoPow 1023
    let n := n - 1023
    if n > 1023 then x * twoPow 1023 * twoPow (min (n - 1023) 1023)
    else x * twoPow n
  else if n < -1022 then
    -- `2 ^ (-1022 + 53)`: the final step lands well inside the subnormal range and rounds once.
    let x := x * twoPow (-969)
    let n := n + 969
    if n < -1022 then x * twoPow (-969) * twoPow (max (n + 969) (-1022))
    else x * twoPow n
  else x * twoPow n

public theorem exponent?_eq_some {x : Float} (h : (x.isFinite && x != 0) = true) :
    x.exponent? = some (x.exponent h) := by simp [exponent?, h]

public theorem exponent?_eq_none {x : Float} (h : (x.isFinite && x != 0) = false) :
    x.exponent? = none := by simp [exponent?, h]

public theorem exponent!_eq {x : Float} (h : (x.isFinite && x != 0) = true) :
    x.exponent! = x.exponent h := by simp [exponent!, h]

end Float

namespace Float32

@[inherit_doc Float.twoPow, expose] public def twoPow (n : Int) : Float32 :=
  if n > 127 then inf
  else if n ≥ -126 then ofBits ((n + 127).toNat.toUInt32 <<< 23)
  else if n ≥ -149 then ofBits ((1 : UInt32) <<< (n + 149).toNat.toUInt32)
  else 0

/--
The exponent of a finite nonzero `x`: the integer `e` with `2 ^ e ≤ |x| < 2 ^ (e + 1)`. This is
`logB` of [IEEE754, 5.3.3]. Subnormal numbers get their true exponent, from `-149` to `-127`.
-/
@[expose] public def exponent (x : Float32) (_ : (x.isFinite && x != 0) = true) : Int :=
  let e := (x.toBits &&& exponentMask) >>> 23
  if e == 0 then ((x.toBits &&& significandMask).toNat.log2 : Int) - 149
  else e.toNat - 127

@[inherit_doc Float.exponent?, expose] public def exponent? (x : Float32) : Option Int :=
  if h : (x.isFinite && x != 0) = true then some (x.exponent h) else none

@[inherit_doc Float.exponent!, expose] public def exponent! (x : Float32) : Int :=
  if h : (x.isFinite && x != 0) = true then x.exponent h
  else panic! "exponent!: zero, infinite or NaN argument"

@[inherit_doc Float.ldexp, expose] public def ldexp (x : Float32) (n : Int) : Float32 :=
  if n > 127 then
    let x := x * twoPow 127
    let n := n - 127
    if n > 127 then x * twoPow 127 * twoPow (min (n - 127) 127)
    else x * twoPow n
  else if n < -126 then
    -- `2 ^ (-126 + 24)`: the final step lands well inside the subnormal range and rounds once.
    let x := x * twoPow (-102)
    let n := n + 102
    if n < -126 then x * twoPow (-102) * twoPow (max (n + 102) (-126))
    else x * twoPow n
  else x * twoPow n

public theorem exponent?_eq_some {x : Float32} (h : (x.isFinite && x != 0) = true) :
    x.exponent? = some (x.exponent h) := by simp [exponent?, h]

public theorem exponent?_eq_none {x : Float32} (h : (x.isFinite && x != 0) = false) :
    x.exponent? = none := by simp [exponent?, h]

public theorem exponent!_eq {x : Float32} (h : (x.isFinite && x != 0) = true) :
    x.exponent! = x.exponent h := by simp [exponent!, h]

end Float32

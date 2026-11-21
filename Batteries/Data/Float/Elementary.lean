/-
 Copyright (c) 2026 François G. Dorais. All rights reserved.
 Released under Apache 2.0 license as described in the file LICENSE.
 Authors: François G. Dorais
-/
module

public import Batteries.Data.Float.ErrorFree
public import Batteries.Data.Float.Scale

/-!
# Elementary functions for `Float` and `Float32` missing from core

* `hypot x y`, `sqrt (x * x + y * y)` without undue overflow or underflow, as in IEEE 754-2019
  §9.2 and C. It uses only arithmetic with a logical model.
* `log1p x = log (1 + x)` and `expm1 x = exp x - 1`, accurate also for small `x`. They are
  computed from core's `log` and `exp`, which are opaque external functions.

## References

* [IEEE754] *IEEE Standard for Floating-Point Arithmetic*, IEEE Std 754-2019.
* [Borges2020] C. F. Borges, *Algorithm 1014: An Improved Algorithm for `hypot(x, y)`*, ACM
  Transactions on Mathematical Software 47 (2020), no. 1, Article 9, doi:10.1145/3428446.
* [Goldberg1991] D. Goldberg, *What Every Computer Scientist Should Know About Floating-Point
  Arithmetic*, ACM Computing Surveys 23 (1991), no. 1, 5–48.
* [Higham2002] N. J. Higham, *Accuracy and Stability of Numerical Algorithms*, 2nd ed., SIAM,
  2002.
-/

namespace Float

/--
`sqrt (a * a + b * b)` for `a ≥ b ≥ 0` in a range where the squares neither overflow nor
underflow, with the fused multiply-add correction step of [Borges2020], which makes the result
correctly rounded in almost all cases.
-/
@[expose] public def hypotCore (a b : Float) : Float :=
  let h := sqrt (fma a a (b * b))
  let x := fma (-b) b (h * h - a * a) + mulErr h h - mulErr a a
  h - x / (2 * h)

/--
`sqrt (x * x + y * y)` without undue overflow or underflow, nearly always correctly rounded
[Borges2020]. As in [IEEE754, 9.2] and C, the result is `inf` when either argument is infinite,
even if the other one is `NaN`. Arguments outside `[2 ^ (-500), 2 ^ 500]` are scaled by powers
of two first.
-/
@[expose] public def hypot (x y : Float) : Float :=
  if x.isInf || y.isInf then inf
  else if x.isNaN || y.isNaN then nan
  else
    let x := x.abs
    let y := y.abs
    let a := if x < y then y else x
    let b := if x < y then x else y
    if a == 0 then 0
    else if a > twoPow 500 then hypotCore (a * twoPow (-600)) (b * twoPow (-600)) * twoPow 600
    else if a < twoPow (-500) then hypotCore (a * twoPow 600) (b * twoPow 600) * twoPow (-600)
    else hypotCore a b

/--
`log (1 + x)`, accurate also when `x` is small, by Kahan's method [Goldberg1991, Theorem 4]:
`log (1 + x) = log u * (x / (u - 1))` with `u = fl(1 + x)`, since the rounding error of `u`
cancels out in the quotient.
-/
@[expose] public def log1p (x : Float) : Float :=
  let u := 1 + x
  if u == 1 || x == inf then x
  else log u * (x / (u - 1))

/--
`exp x - 1`, accurate also when `x` is small, by Kahan's method [Higham2002, §1.14.1]:
`exp x - 1 = (u - 1) * (x / log u)` with `u = fl(exp x)`, since the rounding error of `u`
cancels out in the quotient.
-/
@[expose] public def expm1 (x : Float) : Float :=
  let u := exp x
  if u == 1 then x
  else if u - 1 == -1 || u == inf then u - 1
  else (u - 1) * (x / log u)

end Float

namespace Float32

@[inherit_doc Float.hypotCore, expose] public def hypotCore (a b : Float32) : Float32 :=
  let h := sqrt (fma a a (b * b))
  let x := fma (-b) b (h * h - a * a) + mulErr h h - mulErr a a
  h - x / (2 * h)

/--
`sqrt (x * x + y * y)` without undue overflow or underflow, nearly always correctly rounded
[Borges2020]. As in [IEEE754, 9.2] and C, the result is `inf` when either argument is infinite,
even if the other one is `NaN`. Arguments outside `[2 ^ (-50), 2 ^ 50]` are scaled by powers of
two first.
-/
@[expose] public def hypot (x y : Float32) : Float32 :=
  if x.isInf || y.isInf then inf
  else if x.isNaN || y.isNaN then nan
  else
    let x := x.abs
    let y := y.abs
    let a := if x < y then y else x
    let b := if x < y then x else y
    if a == 0 then 0
    else if a > twoPow 50 then hypotCore (a * twoPow (-90)) (b * twoPow (-90)) * twoPow 90
    else if a < twoPow (-50) then hypotCore (a * twoPow 90) (b * twoPow 90) * twoPow (-90)
    else hypotCore a b

@[inherit_doc Float.log1p, expose] public def log1p (x : Float32) : Float32 :=
  let u := 1 + x
  if u == 1 || x == inf then x
  else log u * (x / (u - 1))

@[inherit_doc Float.expm1, expose] public def expm1 (x : Float32) : Float32 :=
  let u := exp x
  if u == 1 then x
  else if u - 1 == -1 || u == inf then u - 1
  else (u - 1) * (x / log u)

end Float32

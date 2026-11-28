/-
 Copyright (c) 2026 François G. Dorais. All rights reserved.
 Released under Apache 2.0 license as described in the file LICENSE.
 Authors: François G. Dorais
-/
module

/-!
# Error-free transformations for `Float` and `Float32`

The rounding error of a sum or a product of two floating-point numbers is itself a
floating-point number, when nothing overflows (and, for products, nothing underflows). `twoSum`
computes the rounded sum with its error, and `mulErr` the error of a product, with a fused
multiply-add. They are the building blocks of compensated algorithms, such as Kahan's
algorithm for `a * b - c * d` [JeannerodLouvetMuller2013] and compensated summation.

## References

* [Knuth1997] D. E. Knuth, *The Art of Computer Programming, Volume 2: Seminumerical
  Algorithms*, 3rd ed., Addison-Wesley, 1997.
* [JeannerodLouvetMuller2013] C.-P. Jeannerod, N. Louvet and J.-M. Muller, *Further analysis of
  Kahan's algorithm for the accurate computation of 2 × 2 determinants*, Mathematics of
  Computation 82 (2013), no. 284, 2245–2264.
-/

namespace Float

/--
The rounding error `p * q - fl(p * q)` of a product, computed with a fused multiply-add. It is
exact when `p * q` neither overflows nor underflows, and infinite or `NaN` when `p * q`
overflows.
-/
@[expose] public def mulErr (p q : Float) : Float := fma p q (-(p * q))

/--
`(s, e)` with `s = fl(a + b)` and `s + e = a + b` exactly, when nothing overflows. This is the
TwoSum algorithm of [Knuth1997, §4.2.2, Theorem B], which needs no comparison of `a` and `b`.
-/
@[expose] public def twoSum (a b : Float) : Float × Float :=
  let s := a + b
  let b' := s - a
  let a' := s - b'
  (s, (a - a') + (b - b'))

end Float

namespace Float32

@[inherit_doc Float.mulErr, expose] public def mulErr (p q : Float32) : Float32 :=
  fma p q (-(p * q))

@[inherit_doc Float.twoSum, expose] public def twoSum (a b : Float32) : Float32 × Float32 :=
  let s := a + b
  let b' := s - a
  let a' := s - b'
  (s, (a - a') + (b - b'))

end Float32

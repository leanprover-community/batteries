/-
Copyright (c) 2024 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: François G. Dorais
-/

namespace BitVec.GF2

/--
Modular multplication of polynomials over the two-element field GF(2).

The modulus is the polynomial of degree `d` whose coefficients other than the leading `1` are
encoded by the bitvector `m`; `x` and `y` encode the two multiplicands, polynomials of degree less
than `d`.
-/
def mulMod (x y m : BitVec d) : BitVec d :=
  if d = 0 then 0 else Id.run do
    let mut x : BitVec d := x
    let mut r : BitVec d := 0
    for i in [:d-1] do
      r := bif y[i]! then r ^^^ x else r
      x := bif x.msb then x <<< 1 ^^^ m else x <<< 1
    r := bif y[d-1]! then r ^^^ x else r
    return r

/--
Modular exponentiation of polynomials over the two-element field GF(2).

The modulus is the polynomial of degree `d` whose coefficients other than the leading `1` are
encoded by the bitvector `m`; `x` encodes the base, a polynomial of degree less than `d`.
-/
def powMod (x : BitVec d) (n : Nat) (m : BitVec d) : BitVec d :=
  if d = 0 then 0 else Id.run do
    let mut n := n
    let mut x : BitVec d := x
    let mut r : BitVec d := 1
    while n > 1 do
      r := if n % 2 = 1 then mulMod r x m else r
      x := mulMod x x m
      n := n >>> 1
    r := if n = 1 then mulMod r x m else r
    return r

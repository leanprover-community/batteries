/-
Copyright (c) 2025 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: François G. Dorais
-/

import Batteries.Data.Nat.OfBits

namespace Int

/-- `testBit m n` returns whether the `n+1` least significant bit is `1` or `0` -/
@[inline] def testBit : Int → Nat → Bool
  | .ofNat m, n => Nat.testBit m n
  | .negSucc m, n => ! Nat.testBit m n


/--
Construct an integer from bit values (little endian).

If `fill` is false, the result will be a nonnegative integer with all higher unspecified bits zero.
If `fill` is true, the result will be a negative integer with all higher unspecified bits one.
-/
@[inline] def ofBitsFill (f : Fin n → Bool) : (fill : Bool := false) → Int
  | false => Int.ofNat (Nat.ofBits f)
  | true => Int.negSucc (Nat.ofBits fun i => ! f i)

@[simp] theorem testBit_ofBitsFill_lt (f : Fin n → Bool) (fill : Bool) (i) (h : i < n) :
    (ofBitsFill f fill).testBit i = f ⟨i, h⟩ := by
  cases fill <;> simp [ofBitsFill, testBit, h]

@[simp] theorem testBit_ofBitsFill_ge (f : Fin n → Bool) (fill : Bool) (i) (h : n ≤ i) :
    (ofBitsFill f fill).testBit i = fill := by
  cases fill <;> simp [ofBitsFill, testBit, h]

/--
Construct an integer from bit values (little endian). The most significant specified bit is used to
determine the sign:
* If the most significant specified bit is unset then the result will be nonnegative and all
  higher order bits will read as unset.
* If the most significant specified bit is set then the result will be negative and all higher
  order bits will read as set.
-/
@[inline] def ofBits (f : Fin n → Bool) : Int :=
  match n with
  | 0 => 0
  | n+1 => ofBitsFill f (f ⟨n, Nat.lt_succ_self n⟩)

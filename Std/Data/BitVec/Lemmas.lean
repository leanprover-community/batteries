/-
Copyright (c) 2023 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Keizer
-/

import Std.Data.BitVec.Basic

namespace Std.BitVec
variable {w v : Nat}

/-! We add simp-lemmas that rewrite bitvector operations into the equivalent notation -/
@[simp] theorem append_eq (x : BitVec w) (y : BitVec v)   : BitVec.append x y = x ++ y        := rfl
@[simp] theorem shiftLeft_eq (x : BitVec w) (n : Nat)     : BitVec.shiftLeft x n = x <<< n    := rfl
@[simp] theorem ushiftRight_eq (x : BitVec w) (n : Nat)   : BitVec.ushiftRight x n = x >>> n  := rfl
@[simp] theorem not_eq (x : BitVec w)                     : BitVec.not x = ~~~x               := rfl
@[simp] theorem and_eq (x y : BitVec w)                   : BitVec.and x y = x &&& y          := rfl
@[simp] theorem or_eq (x y : BitVec w)                    : BitVec.or x y = x ||| y           := rfl
@[simp] theorem xor_eq (x y : BitVec w)                   : BitVec.xor x y = x ^^^ y          := rfl
@[simp] theorem neg_eq (x : BitVec w)                     : BitVec.neg x = -x                 := rfl
@[simp] theorem add_eq (x y : BitVec w)                   : BitVec.add x y = x + y            := rfl
@[simp] theorem sub_eq (x y : BitVec w)                   : BitVec.sub x y = x - y            := rfl
@[simp] theorem mul_eq (x y : BitVec w)                   : BitVec.mul x y = x * y            := rfl

end Std.BitVec

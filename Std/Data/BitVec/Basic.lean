/-
Copyright (c) 2022 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joe Hendrix, Wojciech Nawrocki, Leonardo de Moura
-/
namespace Std
/-!
We define bitvectors. We choose the `Fin` representation over others for its relative efficiency
(Lean has special support for `Nat`), alignment with `UIntXY` types which are also represented
with `Fin`, and the fact that bitwise operations on `Fin` are already defined. Some other possible
representations are `List Bool`, `{ l : List Bool // l.length = w}`, `Fin w → Bool`.

We also define many bitvector operations from the
[`QF_BV` logic](https://smtlib.cs.uiowa.edu/logics-all.shtml#QF_BV).
of SMT-LIBv2.

TODO(Leo): match the interface to what SMT-LIB provides
-/

/--
A bitvector of the specified width. This is represented as the underlying `Nat` number
in both the runtime and the kernel, inheriting all the special support for `Nat`.
-/
structure BitVec (w : Nat) where
  /-- Bitvector is represented as a `Fin`. -/
  val : Fin (2^w)
  deriving DecidableEq

namespace BitVec

theorem pow_two_gt_zero (w : Nat) : 2^w > 0 := by
  apply Nat.pos_pow_of_pos; decide

/-- The BitVector `i mod 2^n`. -/
protected def ofNat (n : Nat) (i : Nat) : BitVec n :=
  { val := Fin.ofNat' i (pow_two_gt_zero _) }

/-- Given a bitvector `a`, return the underlying `Nat`. -/
protected def toNat (a : BitVec n) : Nat :=
  a.val.val

/-- Return a bitvector `0` of size `n`.  -/
protected def zero (n : Nat) : BitVec n :=
  BitVec.ofNat n 0

instance : Inhabited (BitVec n) where
  default := BitVec.zero n

instance : OfNat (BitVec n) i where
  ofNat := BitVec.ofNat n i

/--
Notation for bit vector literals. `i#n` is a shorthand for `BitVec.ofNat n i`.
TODO: is this a good notation? Do we need it? We can also write `(i : BitVec n)`
-/
syntax:max num noWs "#" noWs num : term
macro_rules | `($i:num#$n:num) => `(BitVec.ofNat $n $i)

/-- Unexpander for bit vector literals. -/
@[app_unexpander BitVec.ofNat] def unexpandBitVecOfNat : Lean.PrettyPrinter.Unexpander
  | `($(_) $n:num $i:num) => `($i:num#$n:num)
  | _                => throw ()

instance : Repr (BitVec n) where
  reprPrec a _ := repr a.val ++ "#" ++ repr n

instance : ToString (BitVec n) where
  toString a := toString (repr a)

/-- Theorem for normalizing the bit vector literal representation. -/
@[simp] theorem ofNat_eq_ofNat : @OfNat.ofNat (BitVec n) i _ = BitVec.ofNat n i := rfl

/-- Addition for bit vectors. -/
protected def add (x y : BitVec n) : BitVec n :=
  { val := x.val + y.val }
/-- Subtraction for bit vectors. -/
protected def sub (x y : BitVec n) : BitVec n :=
  { val := x.val - y.val }
/-- Multiplication for bit vectors. -/
protected def mul (x y : BitVec n) : BitVec n :=
  { val := x.val * y.val }
/-- Modulo for bit vectors. -/
protected def mod (x y : BitVec n) : BitVec n :=
  { val := ⟨x.val % y.val, Nat.lt_of_le_of_lt (Nat.mod_le _ _) x.val.isLt⟩ }
/-- Division for bit vectors. -/
protected def div (x y : BitVec n) : BitVec n :=
  { val := ⟨x.val / y.val, Nat.lt_of_le_of_lt (Nat.div_le_self _ _) x.val.isLt⟩ }
/-- Less than for bit vectors. -/
protected def lt (x y : BitVec n) : Bool :=
  x.val < y.val
/-- Less than or equal to for bit vectors. -/
protected def le (x y : BitVec n) : Bool :=
  x.val ≤ y.val

instance : Add (BitVec n) := ⟨BitVec.add⟩
instance : Sub (BitVec n) := ⟨BitVec.sub⟩
instance : Mul (BitVec n) := ⟨BitVec.mul⟩
instance : Mod (BitVec n) := ⟨BitVec.mod⟩
instance : Div (BitVec n) := ⟨BitVec.div⟩
instance : LT (BitVec n)  := ⟨fun x y => BitVec.lt x y⟩
instance : LE (BitVec n)  := ⟨fun x y => BitVec.le x y⟩

/-- Bitwise and for bit vectors. -/
protected def and (x y : BitVec n) : BitVec n :=
  { val := x.val &&& y.val }
/-- Bitwise or for bit vectors. -/
protected def or (x y : BitVec n) : BitVec n :=
  { val := x.val ||| y.val }
/-- Bitwise xor for bit vectors. -/
protected def xor (x y : BitVec n) : BitVec n :=
  { val := x.val ^^^ y.val }
/-- Complement for bit vectors. -/
protected def complement (x : BitVec n) : BitVec n :=
  0 - (x + .ofNat n 1)
/-- Shift left for bit vectors. -/
protected def shiftLeft (a : BitVec n) (s : Nat) : BitVec n :=
  .ofNat n (a.toNat <<< s)
/-- Shift right for bit vectors. -/
protected def shiftRight (a : BitVec n) (s : Nat) : BitVec n :=
  .ofNat n (a.toNat >>> s)

instance : Complement (BitVec w) := ⟨BitVec.complement⟩
instance : AndOp (BitVec w) := ⟨BitVec.and⟩
instance : OrOp (BitVec w) := ⟨BitVec.or⟩
instance : Xor (BitVec w) := ⟨BitVec.xor⟩
instance : HShiftLeft (BitVec w) Nat (BitVec w) := ⟨BitVec.shiftLeft⟩
instance : HShiftRight (BitVec w) Nat (BitVec w) := ⟨BitVec.shiftRight⟩

/-- Rotate left. -/
def rotateLeft (x : BitVec w) (n : Nat) : BitVec w :=
  x <<< n ||| x >>> (w - n)

/-- Rotate right. -/
def rotateRight (x : BitVec w) (n : Nat) : BitVec w :=
  x >>> n ||| x <<< (w - n)

/-- Append. -/
def append (a : BitVec n) (b : BitVec m) : BitVec (n+m) :=
  .ofNat (n+m) (a.toNat <<< m + b.toNat)

instance : HAppend (BitVec w) (BitVec v) (BitVec (w+v)) := ⟨BitVec.append⟩
/--
Extraction of bits `i` down to `j` from a bit vector of size `n` to yield a
new bitvector of size `i - j + 1`
-/
def extract (i j : Nat) (a : BitVec n) : BitVec (i - j + 1) :=
  BitVec.ofNat _ (a.toNat >>> j)

/--
`repeat_ i x` means concatenate `i` copies of `x`.
Recall that `repeat` is a keyword in Lean.
-/
def repeat_ : (i : Nat) → BitVec w → BitVec (w*i)
  | 0,   _ => 0
  | n+1, x =>
    have hEq : w + w*n = w*(n + 1) := by
      rw [Nat.mul_add, Nat.add_comm, Nat.mul_one]
    hEq ▸ (x ++ repeat_ n x)

/-- Zero extension. -/
def zeroExtend (i : Nat) (x : BitVec w) : BitVec (w+i) :=
  have hEq : w+i = i+w := Nat.add_comm _ _
  hEq ▸ ((0 : BitVec i) ++ x)

/-- Signed extension. -/
def signExtend (i : Nat) (x : BitVec w) : BitVec (w+i) :=
  have hEq : ((w-1) - (w-1) + 1)*i + w = w+i := by
    rw [Nat.sub_self, Nat.zero_add, Nat.one_mul, Nat.add_comm]
  hEq ▸ ((repeat_ i (extract (w-1) (w-1) x)) ++ x)

/-- Return a prefix of size `v` of bit vector `x`. -/
def shrink (v : Nat) (x : BitVec w) : BitVec v :=
  if hZero : 0 < v then
    have hEq : v - 1 + 0 + 1 = v := by
      rw [Nat.add_zero]
      exact Nat.sub_add_cancel hZero
    hEq ▸ x.extract (v - 1) 0
  else 0

/-- Return the `i`-th least significant bit. -/
def lsbGet (x : BitVec w) (i : Nat) : Bool :=
  x.extract i i != 0

end Std.BitVec

/-
Copyright (c) 2022 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joe Hendrix, Wojciech Nawrocki, Leonardo de Moura
-/
import Std.Data.Nat.Init.Lemmas

namespace Std
/-!
We define bitvectors. We choose the `Fin` representation over others for its relative efficiency
(Lean has special support for `Nat`), alignment with `UIntXY` types which are also represented
with `Fin`, and the fact that bitwise operations on `Fin` are already defined. Some other possible
representations are `List Bool`, `{ l : List Bool // l.length = w }`, `Fin w → Bool`.

We also define many bitvector operations from the
[`QF_BV` logic](https://smtlib.cs.uiowa.edu/logics-all.shtml#QF_BV).
of SMT-LIBv2.
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

/-- The BitVector `i mod 2^n`. -/
protected def ofNat (n : Nat) (i : Nat) : BitVec n :=
  { val := Fin.ofNat' i (Nat.pow_two_gt_zero _) }

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
scoped syntax:max num noWs "#" noWs num : term
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

/--
Addition for bit vectors.
SMT-Lib name: `bvadd`.
-/
protected def add (x y : BitVec n) : BitVec n :=
  { val := x.val + y.val }
/--
Subtraction for bit vectors.
-/
protected def sub (x y : BitVec n) : BitVec n :=
  { val := x.val - y.val }
/--
Negation for bit vectors.
SMT-Lib name: `bvneg`.
-/
protected def neg (x : BitVec n) : BitVec n :=
  BitVec.sub 0 x
/-- Bit vector of size `n` where all bits are `1`s -/
protected def allOnes (n : Nat) : BitVec n :=
  BitVec.neg 1
/--
Multiplication for bit vectors.
SMT-Lib name: `bvmul`.
-/
protected def mul (x y : BitVec n) : BitVec n :=
  { val := x.val * y.val }
/--
Modulo for bit vectors.
SMT-Lib name: `bvurem`.
-/
protected def mod (x y : BitVec n) : BitVec n :=
  { val := x.val % y.val }
/--
Division for bit vectors.
SMT-Lib name: `bvudiv`.
Note that `div x 0 = allOnes n` as specified by the SMT-Lib standard.
See the spec at http://smtlib.cs.uiowa.edu/theories-FixedSizeBitVectors.shtml.
This is also consistent with a simple division circuit.
-/
protected def div (x y : BitVec n) : BitVec n :=
  if y = BitVec.zero n then
    BitVec.allOnes n
  else
    { val := x.val / y.val }
/--
Division for bit vectors using the Lean convention where division by zero returns zero.
-/
protected def div' (x y : BitVec n) : BitVec n :=
  { val := x.val / y.val }
/--
Less than for bit vectors.
SMT-Lib name: `bvult`.
-/
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
instance : Neg (BitVec n) := ⟨BitVec.neg⟩
instance : LT (BitVec n)  := ⟨fun x y => BitVec.lt x y⟩
instance : LE (BitVec n)  := ⟨fun x y => BitVec.le x y⟩

/--
Bitwise and for bit vectors.
SMT-Lib name: `bvand`.
-/
protected def and (x y : BitVec n) : BitVec n :=
  { val := x.val &&& y.val }
/--
Bitwise or for bit vectors.
SMT-Lib name: `bvor`.
-/
protected def or (x y : BitVec n) : BitVec n :=
  { val := x.val ||| y.val }
/-- Bitwise xor for bit vectors. -/
protected def xor (x y : BitVec n) : BitVec n :=
  { val := x.val ^^^ y.val }
/--
Complement for bit vectors.
SMT-Lib name: `bvnot`.
-/
protected def not (x : BitVec n) : BitVec n :=
  -(x + .ofNat n 1)
/--
Shift left for bit vectors.
SMT-Lib name: `bvshl`.
-/
protected def shiftLeft (a : BitVec n) (s : Nat) : BitVec n :=
  .ofNat n (a.toNat <<< s)
/--
Shift right for bit vectors.
SMT-Lib name: `bvlshr`.
-/
protected def shiftRight (a : BitVec n) (s : Nat) : BitVec n :=
  .ofNat n (a.toNat >>> s)

instance : Complement (BitVec w) := ⟨BitVec.not⟩
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

/--
Append.
SMT-Lib name: `concat`.
-/
def append (msbs : BitVec n) (lsbs : BitVec m) : BitVec (n+m) :=
  .ofNat (n+m) (msbs.toNat <<< m + lsbs.toNat)

instance : HAppend (BitVec w) (BitVec v) (BitVec (w+v)) := ⟨BitVec.append⟩

/--
Extraction of bits `i` down to `j` from a bit vector of size `n` to yield a
new bitvector of size `i - j + 1`
SMT-Lib name: `extract`.
-/
def extract (i j : Nat) (a : BitVec n) : BitVec (i - j + 1) :=
  BitVec.ofNat _ (a.toNat >>> j)

/--
`replicate i x` means concatenate `i` copies of `x`.
-/
def replicate : (i : Nat) → BitVec w → BitVec (w*i)
  | 0,   _ => 0
  | n+1, x =>
    have hEq : w + w*n = w*(n + 1) := by
      rw [Nat.mul_add, Nat.add_comm, Nat.mul_one]
    hEq ▸ (x ++ replicate n x)

/-- Zero extension. -/
def zeroExtend (i : Nat) (x : BitVec w) : BitVec (w+i) :=
  have hEq : w+i = i+w := Nat.add_comm _ _
  hEq ▸ ((0 : BitVec i) ++ x)

/-- Signed extension. Left-pads with copies of the left-most bit. -/
def signExtend (i : Nat) (x : BitVec w) : BitVec (w+i) :=
  have hEq : ((w-1) - (w-1) + 1)*i + w = w+i := by
    rw [Nat.sub_self, Nat.zero_add, Nat.one_mul, Nat.add_comm]
  hEq ▸ ((replicate i (extract (w-1) (w-1) x)) ++ x)

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

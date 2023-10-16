/-
Copyright (c) 2022 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joe Hendrix, Wojciech Nawrocki, Leonardo de Moura, Mario Carneiro
-/
import Std.Data.Nat.Init.Lemmas
import Std.Tactic.Alias

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
  /-- Construct a `BitVec w` from a number less than `2^w`.
  O(1), because we use `Fin` as the internal representation of a bitvector. -/
  ofFin ::
  /-- Interpret a bitvector as a number less than `2^w`.
  O(1), because we use `Fin` as the internal representation of a bitvector. -/
  toFin : Fin (2^w)
  deriving DecidableEq

namespace BitVec

/-- The `BitVec` with value `i mod 2^n`. Treated as an operation on bitvectors,
this is truncation of the high bits when downcasting and zero-extension when upcasting. -/
protected def ofNat (n : Nat) (i : Nat) : BitVec n where
  toFin := Fin.ofNat' i (Nat.pow_two_pos _)

/-- Given a bitvector `a`, return the underlying `Nat`. This is O(1) because `BitVec` is a
(zero-cost) wrapper around a `Nat`. -/
protected def toNat (a : BitVec n) : Nat := a.toFin.val

/-- Return a bitvector `0` of size `n`. This is the bitvector with all zero bits. -/
protected def zero (n : Nat) : BitVec n := .ofNat n 0

instance : Inhabited (BitVec n) where default := .zero n

instance : OfNat (BitVec n) i where ofNat := .ofNat n i

/-- Notation for bit vector literals. `i#n` is a shorthand for `BitVec.ofNat n i`. -/
-- TODO: is this a good notation? Do we need it? We can also write `(i : BitVec n)`
scoped syntax:max num noWs "#" noWs num : term
macro_rules | `($i:num#$n:num) => `(BitVec.ofNat $n $i)

/-- Unexpander for bit vector literals. -/
@[app_unexpander BitVec.ofNat] def unexpandBitVecOfNat : Lean.PrettyPrinter.Unexpander
  | `($(_) $n:num $i:num) => `($i:num#$n:num)
  | _ => throw ()

instance : Repr (BitVec n) where reprPrec a _ := repr a.toFin ++ "#" ++ repr n

instance : ToString (BitVec n) where toString a := toString (repr a)

/-- Theorem for normalizing the bit vector literal representation. -/
-- TODO: This needs more usage data to assess which direction the simp should go.
@[simp] theorem ofNat_eq_ofNat : @OfNat.ofNat (BitVec n) i _ = BitVec.ofNat n i := rfl

/--
Addition for bit vectors. This can be interpreted as either signed or unsigned addition
modulo `2^n`.

SMT-Lib name: `bvadd`.
-/
protected def add (x y : BitVec n) : BitVec n where toFin := x.toFin + y.toFin
instance : Add (BitVec n) := ⟨BitVec.add⟩

/--
Subtraction for bit vectors. This can be interpreted as either signed or unsigned subtraction
modulo `2^n`.
-/
protected def sub (x y : BitVec n) : BitVec n where toFin := x.toFin - y.toFin
instance : Sub (BitVec n) := ⟨BitVec.sub⟩

/--
Negation for bit vectors. This can be interpreted as either signed or unsigned negation
modulo `2^n`.

SMT-Lib name: `bvneg`.
-/
protected def neg (x : BitVec n) : BitVec n := .sub 0 x
instance : Neg (BitVec n) := ⟨.neg⟩

/-- Bit vector of size `n` where all bits are `1`s -/
def allOnes (n : Nat) : BitVec n := -1

/--
Multiplication for bit vectors. This can be interpreted as either signed or unsigned negation
modulo `2^n`.

SMT-Lib name: `bvmul`.
-/
protected def mul (x y : BitVec n) : BitVec n := ofFin <| x.toFin * y.toFin
instance : Mul (BitVec n) := ⟨.mul⟩

/--
Unsigned modulo for bit vectors.

SMT-Lib name: `bvurem`.
-/
protected def mod (x y : BitVec n) : BitVec n := ofFin <| x.toFin % y.toFin
instance : Mod (BitVec n) := ⟨.mod⟩

/--
Unsigned division for bit vectors using the Lean convention where division by zero returns zero.
-/
protected def div' (x y : BitVec n) : BitVec n := ofFin <| x.toFin / y.toFin

/--
Unsigned division for bit vectors using the
[SMT-Lib convention](http://smtlib.cs.uiowa.edu/theories-FixedSizeBitVectors.shtml)
where division by zero returns the `allOnes` bitvector.

SMT-Lib name: `bvudiv`.
-/
protected def div (x y : BitVec n) : BitVec n := if y = 0 then -1 else .div' x y
instance : Div (BitVec n) := ⟨.div⟩

/--
Unsigned less-than for bit vectors.

SMT-Lib name: `bvult`.
-/
protected def lt (x y : BitVec n) : Bool := x.toFin < y.toFin
instance : LT (BitVec n) where lt x y := x.toFin < y.toFin

/-- Unsigned less-than-or-equal-to for bit vectors. -/
protected def le (x y : BitVec n) : Bool := x.toFin ≤ y.toFin
instance : LE (BitVec n) where le x y := x.toFin ≤ y.toFin

/--
Bitwise AND for bit vectors.

SMT-Lib name: `bvand`.
-/
protected def and (x y : BitVec n) : BitVec n where toFin := x.toFin &&& y.toFin
instance : AndOp (BitVec w) := ⟨.and⟩

/--
Bitwise OR for bit vectors.

SMT-Lib name: `bvor`.
-/
protected def or (x y : BitVec n) : BitVec n where toFin := x.toFin ||| y.toFin
instance : OrOp (BitVec w) := ⟨.or⟩

/-- Bitwise XOR for bit vectors. -/
protected def xor (x y : BitVec n) : BitVec n where toFin := x.toFin ^^^ y.toFin
instance : Xor (BitVec w) := ⟨.xor⟩

/--
Bitwise NOT for bit vectors.

SMT-Lib name: `bvnot`.
-/
protected def not (x : BitVec n) : BitVec n := -(x + .ofNat n 1)
instance : Complement (BitVec w) := ⟨.not⟩

/--
Left shift for bit vectors. The low bits are filled with zeros. As a numeric operation, this is
equivalent to `a * 2^s`, modulo `2^n`.

SMT-Lib name: `bvshl`.
-/
protected def shiftLeft (a : BitVec n) (s : Nat) : BitVec n := .ofNat n (a.toNat <<< s)
instance : HShiftLeft (BitVec w) Nat (BitVec w) := ⟨.shiftLeft⟩

/--
(Logical) right shift for bit vectors. The high bits are filled with zeros.
As a numeric operation, this is equivalent to `a / 2^s`, rounding down.

SMT-Lib name: `bvlshr`.
-/
protected def shiftRight (a : BitVec n) (s : Nat) : BitVec n := .ofNat n (a.toNat >>> s)
instance : HShiftRight (BitVec w) Nat (BitVec w) := ⟨.shiftRight⟩

/--
Rotate left for bit vectors. All the bits of `x` are shifted to higher positions, with the top `n`
bits wrapping around to fill the low bits.
-/
def rotateLeft (x : BitVec w) (n : Nat) : BitVec w := x <<< n ||| x >>> (w - n)

/--
Rotate right for bit vectors. All the bits of `x` are shifted to lower positions, with the
bottom `n` bits wrapping around to fill the high bits.
-/
def rotateRight (x : BitVec w) (n : Nat) : BitVec w := x >>> n ||| x <<< (w - n)

/--
Concatenation of bitvectors. This uses the "big endian" convention that the more significant
input is on the left, so `0xAB#8 ++ 0xCD#8 = 0xABCD#16`.

SMT-Lib name: `concat`.
-/
def append (msbs : BitVec n) (lsbs : BitVec m) : BitVec (n+m) :=
  .ofNat (n + m) (msbs.toNat <<< m ||| lsbs.toNat)

instance : HAppend (BitVec w) (BitVec v) (BitVec (w + v)) := ⟨.append⟩

/--
Extraction of bits `start` to `start + len - 1` from a bit vector of size `n` to yield a
new bitvector of size `len`. If `start + len > n`, then the vector will be zero-padded in the
high bits.
-/
def extract' (start len : Nat) (a : BitVec n) : BitVec len := .ofNat _ (a.toNat >>> start)

/--
Extraction of bits `hi` (inclusive) down to `lo` (inclusive) from a bit vector of size `n` to
yield a new bitvector of size `hi - lo + 1`.

SMT-Lib name: `extract`.
-/
def extract (hi lo : Nat) (a : BitVec n) : BitVec (hi - lo + 1) := extract' lo _ a

/-- `replicate i x` concatenates `i` copies of `x` into a new vector of length `w*i`. -/
def replicate : (i : Nat) → BitVec w → BitVec (w*i)
  | 0,   _ => 0
  | n+1, x =>
    have hEq : w + w*n = w*(n + 1) := by
      rw [Nat.mul_add, Nat.add_comm, Nat.mul_one]
    hEq ▸ (x ++ replicate n x)

/-- Fills a bitvector with `w` copies of the bit `b`. -/
def fill (w : Nat) (b : Bool) : BitVec w := bif b then -1 else 0

/-- Return the `i`-th least significant bit. -/
def lsbGet (x : BitVec w) (i : Nat) : Bool := x.toNat &&& (1 <<< i) != 0

/--
Zero extend vector `x` of length `w` by adding zeros in the high bits until it has length `v`.
If `v < w` then it truncates the high bits instead.
-/
def zeroExtend (v : Nat) (x : BitVec w) : BitVec v := .ofNat v x.toNat

/--
Truncate the high bits of bitvector `x` of length `w`, resulting in a vector of length `v`.
If `v > w` then it zero-extends the vector instead.
-/
alias truncate := zeroExtend

/--
Sign extend a vector of length `w`, extending with `i` additional copies of the most significant
bit in `x`. If `x` is an empty vector, then the sign is treated as zero.
-/
def signExtend (i : Nat) (x : BitVec w) : BitVec (w+i) :=
  Nat.add_comm .. ▸ (fill i (lsbGet x (w-1)) ++ x)

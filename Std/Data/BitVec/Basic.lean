/-
Copyright (c) 2022 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joe Hendrix, Wojciech Nawrocki, Leonardo de Moura, Mario Carneiro, Alex Keizer
-/
import Std.Data.Fin.Basic
import Std.Data.Int.Basic
import Std.Data.Nat.Bitwise
import Std.Tactic.Alias

namespace Std

/-!
We define bitvectors. We choose the `Fin` representation over others for its relative efficiency
(Lean has special support for `Nat`), alignment with `UIntXY` types which are also represented
with `Fin`, and the fact that bitwise operations on `Fin` are already defined. Some other possible
representations are `List Bool`, `{ l : List Bool // l.length = w }`, `Fin w → Bool`.

We define many of the bitvector operations from the
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

/-- `cast eq i` embeds `i` into an equal `BitVec` type. -/
@[inline] def cast (eq : n = m) (i : BitVec n) : BitVec m :=
  .ofFin (Fin.cast (congrArg _ eq) i.toFin)

/-- The `BitVec` with value `i mod 2^n`. Treated as an operation on bitvectors,
this is truncation of the high bits when downcasting and zero-extension when upcasting. -/
protected def ofNat (n : Nat) (i : Nat) : BitVec n where
  toFin := Fin.ofNat' i (Nat.pow_two_pos n)

/-- Given a bitvector `a`, return the underlying `Nat`. This is O(1) because `BitVec` is a
(zero-cost) wrapper around a `Nat`. -/
protected def toNat (a : BitVec n) : Nat := a.toFin.val

/-- Return the bound in terms of toNat. -/
theorem isLt (x : BitVec w) : x.toNat < 2^w := x.toFin.isLt

/-- Return the `i`-th least significant bit or `false` if `i ≥ w`. -/
@[inline] def getLsb (x : BitVec w) (i : Nat) : Bool := x.toNat.testBit i

/-- Return the `i`-th most significant bit or `false` if `i ≥ w`. -/
@[inline] def getMsb (x : BitVec w) (i : Nat) : Bool := i < w && getLsb x (w-1-i)

/-- Return most-significant bit in bitvector. -/
@[inline] protected def msb (a : BitVec n) : Bool := getMsb a 0

/-- Interpret the bitvector as an integer stored in two's complement form. -/
protected def toInt (a : BitVec n) : Int :=
  if a.msb then Int.ofNat a.toNat - Int.ofNat (2^n) else a.toNat

/-- Return a bitvector `0` of size `n`. This is the bitvector with all zero bits. -/
protected def zero (n : Nat) : BitVec n := ⟨0, Nat.pow_two_pos n⟩

instance : Inhabited (BitVec n) where default := .zero n

instance : OfNat (BitVec n) i where ofNat := .ofNat n i

/-- Notation for bit vector literals. `i#n` is a shorthand for `BitVec.ofNat n i`. -/
scoped syntax:max term:max noWs "#" noWs term:max : term
macro_rules | `($i#$n) => `(BitVec.ofNat $n $i)

/- Support for `i#n` notation in patterns.  -/
attribute [match_pattern] BitVec.ofNat

/-- Unexpander for bit vector literals. -/
@[app_unexpander BitVec.ofNat] def unexpandBitVecOfNat : Lean.PrettyPrinter.Unexpander
  | `($(_) $n $i) => `($i#$n)
  | _ => throw ()

/-- Convert bitvector into a fixed-width hex number. -/
protected def toHex {n : Nat} (x : BitVec n) : String :=
  let s := (Nat.toDigits 16 x.toNat).asString
  let t := (List.replicate ((n+3) / 4 - s.length) '0').asString
  t ++ s

instance : Repr (BitVec n) where reprPrec a _ := "0x" ++ (a.toHex : Format) ++ "#" ++ repr n

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
Return the absolute value of a signed bitvector.
-/
protected def abs (s : BitVec n) : BitVec n := if s.msb then .neg s else s

/--
Multiplication for bit vectors. This can be interpreted as either signed or unsigned negation
modulo `2^n`.

SMT-Lib name: `bvmul`.
-/
protected def mul (x y : BitVec n) : BitVec n := ofFin <| x.toFin * y.toFin
instance : Mul (BitVec n) := ⟨.mul⟩

/--
Unsigned division for bit vectors using the Lean convention where division by zero returns zero.
-/
def udiv (x y : BitVec n) : BitVec n := ofFin <| x.toFin / y.toFin
instance : Div (BitVec n) := ⟨.udiv⟩

/--
Unsigned modulo for bit vectors.

SMT-Lib name: `bvurem`.
-/
def umod (x y : BitVec n) : BitVec n := ofFin <| x.toFin % y.toFin
instance : Mod (BitVec n) := ⟨.umod⟩

/--
Unsigned division for bit vectors using the
[SMT-Lib convention](http://smtlib.cs.uiowa.edu/theories-FixedSizeBitVectors.shtml)
where division by zero returns the `allOnes` bitvector.

SMT-Lib name: `bvudiv`.
-/
def smtUDiv (x y : BitVec n) : BitVec n := if y = 0 then -1 else .udiv x y

/--
Signed t-division for bit vectors using the Lean convention where division
by zero returns zero.

```lean
sdiv 7#4 2 = 3#4
sdiv (-9#4) 2 = -4#4
sdiv 5#4 -2 = -2#4
sdiv (-7#4) (-2) = 3#4
```
-/
def sdiv (s t : BitVec n) : BitVec n :=
  match s.msb, t.msb with
  | false, false => udiv s t
  | false, true  => .neg (udiv s (.neg t))
  | true,  false => .neg (udiv (.neg s) t)
  | true,  true  => udiv (.neg s) (.neg t)

/--
Signed division for bit vectors using SMTLIB rules for division by zero.

Specifically, `smtSDiv x 0 = if x >= 0 then -1 else 1`

SMT-Lib name: `bvsdiv`.
-/
def smtSDiv (s t : BitVec n) : BitVec n :=
  match s.msb, t.msb with
  | false, false => smtUDiv s t
  | false, true  => .neg (smtUDiv s (.neg t))
  | true,  false => .neg (smtUDiv (.neg s) t)
  | true,  true  => smtUDiv (.neg s) (.neg t)

/--
Remainder for signed division rounding to zero.

SMT_Lib name: `bvsrem`.
-/
def srem (s t : BitVec n) : BitVec n :=
  match s.msb, t.msb with
  | false, false => umod s t
  | false, true  => umod s (.neg t)
  | true,  false => .neg (umod (.neg s) t)
  | true,  true  => .neg (umod (.neg s) (.neg t))

/--
Remainder for signed division rounded to negative infinity.

SMT_Lib name: `bvsmod`.
-/
def smod (s t : BitVec m) : BitVec m :=
  match s.msb, t.msb with
  | false, false => .umod s t
  | false, true =>
    let u := .umod s (.neg t)
    (if u = BitVec.ofNat m 0 then u else .add u t)
  | true, false =>
    let u := .umod (.neg s) t
    (if u = BitVec.ofNat m 0 then u else .sub t u)
  | true, true => .neg (.umod (.neg s) (.neg t))

/--
Unsigned less-than for bit vectors.

SMT-Lib name: `bvult`.
-/
protected def ult (x y : BitVec n) : Bool := x.toFin < y.toFin
instance : LT (BitVec n) where lt x y := x.toFin < y.toFin

/--
Unsigned less-than-or-equal-to for bit vectors.

SMT-Lib name: `bvule`.
-/
protected def ule (x y : BitVec n) : Bool := x.toFin ≤ y.toFin

instance : LE (BitVec n) where le x y := x.toFin ≤ y.toFin

/--
Signed less-than for bit vectors.

```lean
BitVec.slt 6#4 7 = true
BitVec.slt 7#4 8 = false
```
SMT-Lib name: `bvslt`.
-/
protected def slt (x y : BitVec n) : Bool := x.toInt < y.toInt

/--
Signed less-than-or-equal-to for bit vectors.

SMT-Lib name: `bvsle`.
-/
protected def sle (x y : BitVec n) : Bool := x.toInt ≤ y.toInt

/--
Bitwise AND for bit vectors.

```lean
0b1010#4 &&& 0b0110#4 = 0b0010#4
```

SMT-Lib name: `bvand`.
-/
protected def and (x y : BitVec n) : BitVec n where toFin :=
   ⟨x.toNat &&& y.toNat, Nat.and_lt_two_pow x.toNat y.isLt⟩
instance : AndOp (BitVec w) := ⟨.and⟩

/--
Bitwise OR for bit vectors.

```lean
0b1010#4 ||| 0b0110#4 = 0b1110#4
```

SMT-Lib name: `bvor`.
-/
protected def or (x y : BitVec n) : BitVec n where toFin :=
   ⟨x.toNat ||| y.toNat, Nat.or_lt_two_pow x.isLt y.isLt⟩
instance : OrOp (BitVec w) := ⟨.or⟩

/--
 Bitwise XOR for bit vectors.

```lean
0b1010#4 ^^^ 0b0110#4 = 0b1100#4
```

SMT-Lib name: `bvxor`.
-/
protected def xor (x y : BitVec n) : BitVec n where toFin :=
   ⟨x.toNat ^^^ y.toNat, Nat.xor_lt_two_pow x.isLt y.isLt⟩
instance : Xor (BitVec w) := ⟨.xor⟩

/--
Bitwise NOT for bit vectors.

```lean
~~~(0b0101#4) == 0b1010
```
SMT-Lib name: `bvnot`.
-/
protected def not (x : BitVec n) : BitVec n :=
  let ones := .ofFin ⟨(1 <<< n).pred,
    n.one_shiftLeft.symm ▸
      (Nat.pred_lt <| Nat.ne_of_gt <| Nat.pos_pow_of_pos _ <| Nat.zero_lt_succ _)⟩;
  ones ^^^ x
instance : Complement (BitVec w) := ⟨.not⟩

/-- The `BitVec` with value `(2^n + (i mod 2^n)) mod 2^n`.  -/
protected def ofInt (n : Nat) (i : Int) : BitVec n :=
  match i with
  | Int.ofNat a => .ofNat n a
  | Int.negSucc a => ~~~.ofNat n a

/--
Left shift for bit vectors. The low bits are filled with zeros. As a numeric operation, this is
equivalent to `a * 2^s`, modulo `2^n`.

SMT-Lib name: `bvshl` except this operator uses a `Nat` shift value.
-/
protected def shiftLeft (a : BitVec n) (s : Nat) : BitVec n := .ofNat n (a.toNat <<< s)
instance : HShiftLeft (BitVec w) Nat (BitVec w) := ⟨.shiftLeft⟩

/--
(Logical) right shift for bit vectors. The high bits are filled with zeros.
As a numeric operation, this is equivalent to `a / 2^s`, rounding down.

SMT-Lib name: `bvlshr` except this operator uses a `Nat` shift value.
-/
def ushiftRight (a : BitVec n) (s : Nat) : BitVec n :=
  ⟨a.toNat >>> s, by
  let ⟨a, lt⟩ := a
  simp only [BitVec.toNat, Nat.shiftRight_eq_div_pow, Nat.div_lt_iff_lt_mul (Nat.pow_two_pos s)]
  rw [←Nat.mul_one a]
  exact Nat.mul_lt_mul_of_lt_of_le' lt (Nat.pow_two_pos s) (Nat.le_refl 1)⟩

instance : HShiftRight (BitVec w) Nat (BitVec w) := ⟨.ushiftRight⟩

/--
Arithmetic right shift for bit vectors. The high bits are filled with the
most-significant bit.
As a numeric operation, this is equivalent to `a.toInt >>> s`.

SMT-Lib name: `bvashr` except this operator uses a `Nat` shift value.
-/
def sshiftRight (a : BitVec n) (s : Nat) : BitVec n := .ofInt n (a.toInt >>> s)

instance {n} : HShiftLeft  (BitVec m) (BitVec n) (BitVec m) := ⟨fun x y => x <<< y.toNat⟩
instance {n} : HShiftRight (BitVec m) (BitVec n) (BitVec m) := ⟨fun x y => x >>> y.toNat⟩

/--
Rotate left for bit vectors. All the bits of `x` are shifted to higher positions, with the top `n`
bits wrapping around to fill the low bits.

```lean
rotateLeft  0b0011#4 3 = 0b1001
```
SMT-Lib name: `rotate_left` except this operator uses a `Nat` shift amount.
-/
def rotateLeft (x : BitVec w) (n : Nat) : BitVec w := x <<< n ||| x >>> (w - n)

/--
Rotate right for bit vectors. All the bits of `x` are shifted to lower positions, with the
bottom `n` bits wrapping around to fill the high bits.

```lean
rotateRight 0b01001#5 1 = 0b10100
```
SMT-Lib name: `rotate_right` except this operator uses a `Nat` shift amount.
-/
def rotateRight (x : BitVec w) (n : Nat) : BitVec w := x >>> n ||| x <<< (w - n)

/--
A version of `zeroExtend` that requires a proof, but is a noop.
-/
def zeroExtend' {n w : Nat} (le : n ≤ w) (x : BitVec n)  : BitVec w :=
  ⟨x.toNat, by
    apply Nat.lt_of_lt_of_le x.isLt
    exact Nat.pow_le_pow_of_le_right (by trivial) le⟩

/--
`shiftLeftZeroExtend x n` returns `zeroExtend (w+n) x <<< n` without
needing to compute `x % 2^(2+n)`.
-/
def shiftLeftZeroExtend (msbs : BitVec w) (m : Nat) : BitVec (w+m) :=
  let shiftLeftLt {x : Nat} (p : x < 2^w) (m : Nat) : x <<< m < 2^(w+m) := by
        simp [Nat.shiftLeft_eq, Nat.pow_add]
        apply Nat.mul_lt_mul_of_pos_right p
        exact (Nat.pow_two_pos m)
  ⟨msbs.toNat <<< m, shiftLeftLt msbs.isLt m⟩

/--
Concatenation of bitvectors. This uses the "big endian" convention that the more significant
input is on the left, so `0xAB#8 ++ 0xCD#8 = 0xABCD#16`.

SMT-Lib name: `concat`.
-/
def append (msbs : BitVec n) (lsbs : BitVec m) : BitVec (n+m) :=
  shiftLeftZeroExtend msbs m ||| zeroExtend' (Nat.le_add_left m n) lsbs

instance : HAppend (BitVec w) (BitVec v) (BitVec (w + v)) := ⟨.append⟩

/--
Extraction of bits `start` to `start + len - 1` from a bit vector of size `n` to yield a
new bitvector of size `len`. If `start + len > n`, then the vector will be zero-padded in the
high bits.
-/
def extractLsb' (start len : Nat) (a : BitVec n) : BitVec len := .ofNat _ (a.toNat >>> start)

/--
Extraction of bits `hi` (inclusive) down to `lo` (inclusive) from a bit vector of size `n` to
yield a new bitvector of size `hi - lo + 1`.

SMT-Lib name: `extract`.
-/
def extractLsb (hi lo : Nat) (a : BitVec n) : BitVec (hi - lo + 1) := extractLsb' lo _ a

-- TODO: write this using multiplication
/-- `replicate i x` concatenates `i` copies of `x` into a new vector of length `w*i`. -/
def replicate : (i : Nat) → BitVec w → BitVec (w*i)
  | 0,   _ => 0
  | n+1, x =>
    have hEq : w + w*n = w*(n + 1) := by
      rw [Nat.mul_add, Nat.add_comm, Nat.mul_one]
    hEq ▸ (x ++ replicate n x)

/-- Fills a bitvector with `w` copies of the bit `b`. -/
def fill (w : Nat) (b : Bool) : BitVec w := bif b then -1 else 0

/--
Zero extend vector `x` of length `w` by adding zeros in the high bits until it has length `v`.
If `v < w` then it truncates the high bits instead.

SMT-Lib name: `zero_extend`.
-/
def zeroExtend (v : Nat) (x : BitVec w) : BitVec v :=
  if h : w ≤ v then
    zeroExtend' h x
  else
    .ofNat v x.toNat

/--
Truncate the high bits of bitvector `x` of length `w`, resulting in a vector of length `v`.
If `v > w` then it zero-extends the vector instead.
-/
alias truncate := zeroExtend

/--
Sign extend a vector of length `w`, extending with `i` additional copies of the most significant
bit in `x`. If `x` is an empty vector, then the sign is treated as zero.

SMT-Lib name: `sign_extend`.
-/
def signExtend (v : Nat) (x : BitVec w) : BitVec v := .ofInt v x.toInt

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
@[simp] theorem zero_eq                                   : BitVec.zero n = 0#n               := rfl

@[simp] theorem cast_ofNat {n m : Nat} (h : n = m) (x : Nat) :
    cast h (BitVec.ofNat n x) = BitVec.ofNat m x := by
  subst h; rfl

@[simp] theorem cast_cast {n m k : Nat} (h₁ : n = m) (h₂ : m = k) (x : BitVec n) :
    cast h₂ (cast h₁ x) = cast (h₁ ▸ h₂) x :=
  rfl

@[simp] theorem cast_eq {n : Nat} (h : n = n) (x : BitVec n) :
    cast h x = x :=
  rfl

/-- Turn a `Bool` into a bitvector of length `1` -/
def ofBool (b : Bool) : BitVec 1 := cond b 1 0

@[simp] theorem ofBool_false : ofBool false = 0 := by trivial
@[simp] theorem ofBool_true  : ofBool true  = 1 := by trivial

/-- The empty bitvector -/
abbrev nil : BitVec 0 := 0

/-!
### Cons and Concat
We give special names to the operations of adding a single bit to either end of a bitvector.
We follow the precedent of `Vector.cons`/`Vector.concat` both for the name, and for the decision
to have the resulting size be `n + 1` for both operations (rather than `1 + n`, which would be the
result of appending a single bit to the front in the naive implementation).
-/

/-- Append a single bit to the end of a bitvector, using big endian order (see `append`).
    That is, the new bit is the least significant bit. -/
def concat {n} (msbs : BitVec n) (lsb : Bool) : BitVec (n+1) := msbs ++ (ofBool lsb)

/-- Prepend a single bit to the front of a bitvector, using big endian order (see `append`).
    That is, the new bit is the most significant bit. -/
def cons {n} (msb : Bool) (lsbs : BitVec n) : BitVec (n+1) :=
  ((ofBool msb) ++ lsbs).cast (Nat.add_comm ..)

/-- All empty bitvectors are equal -/
instance : Subsingleton (BitVec 0) where
  allEq := by intro ⟨0, _⟩ ⟨0, _⟩; rfl

/-- Every bitvector of length 0 is equal to `nil`, i.e., there is only one empty bitvector -/
theorem eq_nil : ∀ (x : BitVec 0), x = nil
  | ofFin ⟨0, _⟩ => rfl

theorem append_ofBool (msbs : BitVec w) (lsb : Bool) :
    msbs ++ ofBool lsb = concat msbs lsb :=
  rfl

theorem ofBool_append (msb : Bool) (lsbs : BitVec w) :
    ofBool msb ++ lsbs = (cons msb lsbs).cast (Nat.add_comm ..) :=
  rfl

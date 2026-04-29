/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wrenna Robson
-/

module

@[expose] public section

namespace Nat

/-! ## Basic functions -/

/-- `bit b n` appends the digit `b` to the little end of the binary representation of `n`. -/
def bit (b : Bool) : Nat → Nat | 0 => b.toNat | n + 1 => bit b n + 2

/-- Efficient implementation of bit. -/
@[inline] def bitImpl (b : Bool) (n : Nat) : Nat := n <<< 1 + b.toNat

@[csimp] theorem bit_eq_bitImpl : bit = bitImpl := funext <| fun _ => funext <| fun _ => by
  fun_induction bit <;> grind [bitImpl, shiftLeft_succ]

/-- `isOdd n` returns `true` just when `n` is odd -/
def isOdd : Nat → Bool | 0 => false | 1 => true | n + 2 => n.isOdd

/-- Efficient implementation of isOdd. -/
@[inline] def isOddImpl (n : Nat) : Bool := 1 &&& n != 0

@[csimp] theorem isOdd_eq_isOddImpl : isOdd = isOddImpl := funext <| fun _ => by
  fun_induction isOdd <;> grind [isOddImpl]

/-- `isEven n` returns `true` just when `n` is even -/
def isEven (n : Nat) : Bool := !n.isOdd

/-- Efficient implementation of isOdd. -/
@[inline] def isEvenImpl (n : Nat) : Bool := !(1 &&& n != 0)

@[csimp] theorem isEven_eq_isEvenImpl : isEven = isEvenImpl := funext <| fun _ => by
  unfold isEven; fun_induction isOdd <;> grind [isEvenImpl]

/-- `divTwo n` is `n / 2` (rounded down). -/
def divTwo : Nat → Nat | 0 | 1 => 0 | n + 2 => n.divTwo + 1

/-- Efficient implementation of divTwo. -/
@[inline] def divTwoImpl (n : Nat) : Nat := n >>> 1

@[csimp] theorem divTwo_eq_divTwoImpl : divTwo = divTwoImpl := funext <| fun _ => by
  fun_induction divTwo <;> grind [divTwoImpl, Nat.shiftRight_succ]

/-- `isOdd` and `divTwo` as a single map to a tuple. -/
def isOddDivTwo (n : Nat) : Bool × Nat := (n.isOdd, n.divTwo)

/-! ## Recursion principles -/

/-- A recursion principle over the even natural numbers. -/
@[elab_as_elim, specialize]
protected def evenRec {motive : (n : Nat) → n.isEven → Sort u} (zero : motive 0 rfl)
    (add_two : ∀ n h, motive n h → motive (n + 2) h) :
    (n : Nat) → (hn : n.isEven) → motive n hn
  | 0, _ => zero | n + 2, h => add_two n h (n.evenRec zero add_two h)

/-- A recursion principle over the odd natural numbers. -/
@[elab_as_elim, specialize]
protected def oddRec {motive : (n : Nat) → n.isOdd → Sort u} (one : motive 1 rfl)
    (add_two : ∀ n h, motive n h → motive (n + 2) h) :
    (n : Nat) → (hn : n.isOdd) → motive n hn
  | 1, _ => one | n + 2, h => add_two n h (n.oddRec one add_two h)

/-- By starting with `0` and `1` base cases and given we can induct over even and odd
  numbers, we can achieve a motive for any `n`. -/
@[elab_as_elim, specialize]
protected def parityRec {motive : Nat → Sort u} (zero : motive 0) (one : motive 1)
    (add_two : ∀ n, motive n → motive (n + 2)) (n : Nat) : motive n :=
  if hn : n.isOdd then n.oddRec one (fun n _ => add_two n) hn
  else n.evenRec zero (fun n _ => add_two n) (Bool.not_eq.mpr hn)

/-- A base-2 recursion principle for natural numbers. We have base cases for `0` and `1`: for all
  other natural numbers `n + 2`, the case for `n.divTwo + 1` suffices. -/
@[elab_as_elim, specialize]
protected def divTwoRec {motive : Nat → Sort u} (zero : motive 0) (one : motive 1)
    (add_two : ∀ n, motive (n.divTwo + 1) → motive (n + 2)) : ∀ n, motive n
  | 0 => zero | 1 => one | n + 2 => add_two n <| (n.divTwo + 1).divTwoRec zero one add_two
  decreasing_by fun_induction divTwo <;> grind

/-- Iterates over the binary digits of a natural number, from least significant to most significant.
    Base cases are provided for `0`, `1`. All other numbers are folded via their binary digits. -/
@[inline] protected def bitElim {α} (zero one : α) (bit : Bool → α → α) : Nat → α :=
  Nat.divTwoRec zero one (bit ∘ isOdd)

/-- Iterates over the binary digits of a natural number, from least significant to most significant.
    A base case is provided for `0`. Thereafter we iterate over the number's bits. -/
protected abbrev bitElimFromZero {α : Sort u} (zero : α) (bit : Bool → α → α) :
  Nat → α := Nat.bitElim zero (bit true zero) bit

/-! ## Recursive functions -/

/-- `size n` : Returns the size of a natural number in
bits i.e. the length of its binary representation -/
def size (n : Nat) : Nat := n.bitElimFromZero 0 (Function.const Bool succ)

/-- `popcount n` : Returns the number of set bits in a natural number. -/
def popcount (n : Nat) : Nat := n.bitElimFromZero 0 (flip (· + ·.toNat))

/-- `bitsList n` returns a list of Bools which correspond to the binary representation of n, where
the head of the list represents the least significant bit. -/
def bitsList (n : Nat) : List Bool := n.bitElimFromZero [] List.cons

/-- `ofBitsList bs` constructs a natural number from a list of bits using little endian
  convention. -/
def ofBitsList (xs : List Bool) : Nat := xs.foldr bit 0

/-- `leastBitsList n` returns, for non-zero `n`, `some l`, where `l` is a list of the bits below the
  most significant bit of `n`. It returns `none` just when `n = 0`. -/
def leastBitsList (n : Nat) : Option (List Bool) :=
  n.bitElim none (some []) (Option.map <| List.cons ·)

/-- `ofLeastBitsList oxs` constructs a natural number from the bits below its most significant
  bit (and is `0` just when the `Option` is empty). -/
def ofLeastBitsList (oxs : Option (List Bool)) : Nat :=
  oxs.elim 0 (ofBitsList ∘ (· ++ [true]))

/-- Apply an unary boolean operator bitwise on a natural number. -/
@[specialize] def bitUnary (f : Bool → Bool) (n : Nat) : Nat := n.bitElimFromZero 0 (bit ∘ f)

/-- Apply a binary boolean operator bitwise on a pair of natural numbers. -/
@[specialize] def bitBinary (f : Bool → Bool → Bool) (n : Nat) : Nat → Nat :=
  n.bitElimFromZero (bitUnary <| f false) (((bit.uncurry ∘ · ∘ isOddDivTwo) ∘ ·) ∘ Prod.map ∘ f)

end Nat

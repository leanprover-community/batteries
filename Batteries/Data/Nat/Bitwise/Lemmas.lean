/-
Copyright (c) 2025 François G. Dorais, Wrenna Robson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: François G. Dorais, Wrenna Robson
-/

module

public import Batteries.Data.Nat.Bitwise.Basic

@[expose] public section

/-! # Bitwise Lemmas

This module defines properties of the bitwise operations on natural numbers.

This file is complements `Init.Data.Nat.Bitwise.Lemmas` with properties that
are not necessary for the bitvector library.
-/

namespace Nat

/-! ### and -/

@[simp] theorem and_self_left (a b : Nat) : a &&& (a &&& b) = a &&& b := by
  apply Nat.eq_of_testBit_eq; simp

@[simp] theorem and_self_right (a b : Nat) : ((a &&& b) &&& b) = (a &&& b) := by
  apply Nat.eq_of_testBit_eq; simp

theorem and_left_comm (x y z : Nat) : x &&& (y &&& z) = y &&& (x &&& z) := by
  apply Nat.eq_of_testBit_eq; simp [Bool.and_left_comm]

theorem and_right_comm (x y z : Nat) : (x &&& y) &&& z = (x &&& z) &&& y := by
  apply Nat.eq_of_testBit_eq; simp [Bool.and_right_comm]

/-! ### or -/

@[simp] theorem or_self_left (a b : Nat) : a ||| (a ||| b) = a ||| b := by
  apply Nat.eq_of_testBit_eq; simp

@[simp] theorem or_self_right (a b : Nat) : (a ||| b) ||| b = a ||| b := by
  apply Nat.eq_of_testBit_eq; simp

theorem or_left_comm (x y z : Nat) : x ||| (y ||| z) = y ||| (x ||| z) := by
  apply Nat.eq_of_testBit_eq; simp [Bool.or_left_comm]

theorem or_right_comm (x y z : Nat) : (x ||| y) ||| z = (x ||| z) ||| y := by
  apply Nat.eq_of_testBit_eq; simp [Bool.or_right_comm]

/-! ### xor -/

theorem xor_left_comm (x y z : Nat) : x ^^^ (y ^^^ z) = y ^^^ (x ^^^ z) := by
  apply Nat.eq_of_testBit_eq; simp only [testBit_xor, Bool.xor_left_comm, implies_true]

theorem xor_right_comm (x y z : Nat) : (x ^^^ y) ^^^ z = (x ^^^ z) ^^^ y := by
  apply Nat.eq_of_testBit_eq; simp only [testBit_xor, Bool.xor_right_comm, implies_true]

@[simp] theorem xor_xor_cancel_left (x y : Nat) : x ^^^ (x ^^^ y) = y := by
  apply Nat.eq_of_testBit_eq; simp

@[simp] theorem xor_xor_cancel_right (x y : Nat) : (x ^^^ y) ^^^ y = x := by
  apply Nat.eq_of_testBit_eq; simp

theorem eq_of_xor_eq_zero {x y : Nat} : x ^^^ y = 0 → x = y := by
  intro h; rw [← xor_xor_cancel_left x y, h, xor_zero]

@[simp] theorem xor_eq_zero_iff {x y : Nat} : x ^^^ y = 0 ↔ x = y :=
  ⟨eq_of_xor_eq_zero, fun | rfl => Nat.xor_self _⟩

theorem xor_ne_zero_iff {x y : Nat} : x ^^^ y ≠ 0 ↔ x ≠ y := by simp

/-! ### injectivity lemmas -/

theorem xor_right_injective {x : Nat} : Function.Injective (x ^^^ ·) := by
  intro y z h; rw [← xor_xor_cancel_left x y, ← xor_xor_cancel_left x z]; simp only [h]

theorem xor_left_injective {x : Nat} : Function.Injective (· ^^^ x) := by
  intro y z h; rw [← xor_xor_cancel_right y x, ← xor_xor_cancel_right z x]; simp only [h]

@[simp] theorem xor_right_inj {x y z : Nat} : x ^^^ y = x ^^^ z ↔ y = z :=
  ⟨(xor_right_injective ·), fun | rfl => rfl⟩

@[simp] theorem xor_left_inj {x y z : Nat} : x ^^^ z = y ^^^ z ↔ x = y :=
  ⟨(xor_left_injective ·), fun | rfl => rfl⟩

theorem and_or_right_injective {m x y : Nat} : x &&& m = y &&& m → x ||| m = y ||| m → x = y := by
  intro ha ho
  apply Nat.eq_of_testBit_eq
  intro i
  rw [← Bool.and_or_inj_right_iff (m := m.testBit i)]
  simp [← testBit_and, ← testBit_or, ha, ho]

theorem and_or_right_inj {m x y : Nat} : x &&& m = y &&& m ∧ x ||| m = y ||| m ↔ x = y :=
  ⟨fun ⟨ha, ho⟩ => and_or_right_injective ha ho, fun | rfl => ⟨rfl, rfl⟩⟩

theorem and_or_left_injective {m x y : Nat} : m &&& x = m &&& y → m ||| x = m ||| y → x = y := by
  intro ha ho
  apply Nat.eq_of_testBit_eq
  intro i
  rw [← Bool.and_or_inj_left_iff (m := m.testBit i)]
  simp [← testBit_and, ← testBit_or, ha, ho]

theorem and_or_left_inj {m x y : Nat} : m &&& x = m &&& y ∧ m ||| x = m ||| y ↔ x = y :=
  ⟨fun ⟨ha, ho⟩ => and_or_left_injective ha ho, fun | rfl => ⟨rfl, rfl⟩⟩

/-! ### isOdd -/

@[simp, grind =] theorem isOdd_zero : isOdd 0 = false := rfl
@[simp, grind =] theorem isOdd_one : isOdd 1 = true := rfl
@[simp, grind =] theorem isOdd_add_two {n} : isOdd (n + 2) = isOdd n := rfl

theorem toNat_isOdd {n} : (isOdd n).toNat = n % 2 := by
  fun_induction isOdd <;> grind

@[simp, grind =] theorem isOdd_add_one {n} : isOdd (n + 1) = isEven n := by
  unfold isEven; fun_induction isOdd <;> grind

theorem isOdd_val {n} : isOdd n = n.testBit 0 := congrFun isOdd_eq_isOddImpl n

theorem testBit_zero_eq_isOdd {n} : n.testBit 0 = isOdd n := isOdd_val.symm

/-! ### isEven -/

@[simp, grind =] theorem isEven_zero : isEven 0 = true := rfl
@[simp, grind =] theorem isEven_one : isEven 1 = false := rfl
@[simp, grind =] theorem isEven_add_two {n} : isEven (n + 2) = isEven n := rfl

theorem toNat_isEven {n} : (isEven n).toNat = 1 - n % 2 := by
  unfold isEven; fun_induction isOdd <;> grind

@[simp, grind =] theorem isEven_add_one {n} : isEven (n + 1) = isOdd n := by cases n <;> simp

theorem isEven_val {n} : isEven n = !(n.testBit 0) := congrFun isEven_eq_isEvenImpl n

/-! ### isOdd, isEven -/

@[simp, grind =]
theorem not_isOdd {n} : (!(isOdd n)) = isEven n := rfl

@[simp, grind =]
theorem not_isEven {n} : (!(isEven n)) = isOdd n := Bool.not_not _

theorem isOdd_add {m n} : isOdd (m + n) = (isOdd m ^^ isOdd n) := by
  fun_induction isOdd n <;> try grind
  simp

theorem isOdd_mul {m n} : isOdd (m * n) = (isOdd m && isOdd n) := by
  fun_induction isOdd n <;> grind [mul_succ, isOdd_add]

theorem isEven_add {m n} : isEven (m + n) = (isEven m ^^ isOdd n) := by
  unfold isEven; fun_induction isOdd n <;> grind

theorem isEven_mul {m n} : isEven (m * n) = (isEven m || isEven n) := by
  unfold isEven; fun_induction isOdd n <;> try grind
  simpa [succ_eq_add_one, mul_succ, isEven_add]

@[simp, grind =] theorem isOdd_eq_false_iff : isOdd n = false ↔ isEven n = true := by grind [isEven]
@[simp, grind =] theorem isEven_eq_false_iff : isEven n = false ↔ isOdd n = true := by grind
@[simp] theorem isOdd_ne_iff {b} : isOdd n ≠ b ↔ isEven n = b := by grind
@[simp] theorem isEven_ne_iff {b} : isEven n ≠ b ↔ isOdd n = b := by grind

theorem isEven_or_isOdd {n : Nat} : n.isEven ∨ n.isOdd := by grind

theorem isEven_bor_isOdd {n : Nat} : n.isEven || n.isOdd := by grind

theorem isEven_toNat_add_isOdd_toNat {n : Nat} : n.isEven.toNat + n.isOdd.toNat = 1 := by grind

/-! ### divTwo -/

@[simp, grind =] theorem divTwo_zero : divTwo 0 = 0 := rfl
@[simp, grind =] theorem divTwo_one : divTwo 1 = 0 := rfl
@[simp, grind =] theorem divTwo_add_two {n} : divTwo (n + 2) = divTwo n + 1 := rfl

theorem divTwo_add_one {n} : divTwo (n + 1) = n.divTwo + n.isOdd.toNat := by
  fun_induction divTwo <;> grind

theorem divTwo_val {n} : divTwo n = n / 2 := congrFun divTwo_eq_divTwoImpl n

theorem testBit_add_one_eq_testBit_divTwo {n i : Nat} :
    n.testBit (i + 1) = n.divTwo.testBit i := by rw [testBit_add_one, divTwo_val]

theorem testBit_divTwo {n i : Nat} : n.divTwo.testBit i = n.testBit (i + 1) :=
  testBit_add_one_eq_testBit_divTwo.symm

@[grind =] theorem lt_divTwo_iff {n m : Nat} : m < n.divTwo ↔ 2 * m < n - 1 := by
  fun_induction divTwo generalizing m <;> cases m <;> grind

@[grind =] theorem le_divTwo_iff {n m : Nat} : m ≤ n.divTwo ↔ 2 * m ≤ n := by
  fun_induction divTwo generalizing m <;> cases m <;> grind

@[grind =] theorem divTwo_lt_iff {n m : Nat} : n.divTwo < m ↔ n < 2 * m := by
  fun_induction divTwo generalizing m <;> cases m <;> grind

@[grind =] theorem divTwo_le_iff {n m : Nat} : n.divTwo ≤ m ↔ n ≤ 2 * m + 1 := by
  fun_induction divTwo generalizing m <;> cases m <;> grind

theorem divTwo_eq_iff {n m : Nat} : n.divTwo = m ↔ 2 * m ≤ n ∧ n ≤ 2 * m + 1 :=
  Nat.le_antisymm_iff.trans (by grind)

@[simp, grind .] theorem divTwo_eq_zero_iff {n : Nat} : n.divTwo = 0 ↔ n = 0 ∨ n = 1 := by
  rw [divTwo_eq_iff]; grind

/-! ### testBit -/

theorem testBit_one {i} : testBit 1 i = decide (i = 0) := by cases i <;> grind

theorem testBit_add_two_left {i} : testBit (n + 2) i =
    if i = 0 then n.isOdd else (n.divTwo + 1).testBit (i - 1) := by
  cases i <;> grind [testBit_zero_eq_isOdd, testBit_add_one_eq_testBit_divTwo]

/-! ### bit -/

@[simp, grind =] theorem bit_zero {b} : bit b 0 = b.toNat := rfl
@[simp, grind =] theorem bit_add_one {b n} : bit b (n + 1) = n.bit b + 2 := rfl

@[grind =]
theorem bit_add_bit (b d : Bool) (n m : Nat) :
    bit b n + bit d m =
    bif b then bit (!d) (n + m + d.toNat) else bit d (n + m) := by
  fun_induction m.bit d
  · fun_induction n.bit b <;> grind [cases Bool]
  · grind [cases Bool]

theorem bit_add_bit_false (b : Bool) (n m : Nat) :
    bit b n + bit false m = bit b (n + m) := by grind

theorem bit_false_add_bit (b : Bool) (n m : Nat) :
    bit false n + bit b m = bit b (n + m) := by grind

theorem bit_true_add_bit (b : Bool) (n m : Nat) :
    bit true n + bit b m = bit (!b) (n + m + b.toNat) := by grind

theorem bit_add_bit_true (b : Bool) (n m : Nat) :
    bit b n + bit true m = bit (!b) (n + m + b.toNat) := by grind

theorem bit_false_add_one (n : Nat) : bit false n + 1 = bit true n := bit_false_add_bit true n 0

theorem bit_true_add_one (n : Nat) : bit true n + 1 = bit false (n + 1) :=
  bit_true_add_bit true n 0

theorem bit_add_eq_bit_bne_add_toNat_and (b d : Bool) (n m : Nat) :
    bit b n + bit d m = bit (b != d) (n + m + (b && d).toNat) := by
  cases b <;> cases d <;> apply bit_add_bit

@[grind =] theorem bit_false {n} : bit false n = 2 * n := by fun_induction bit <;> grind
@[grind =] theorem bit_true {n} : bit true n = 2 * n + 1 := by grind [bit_false_add_one]

theorem bit_val {b n} : n.bit b = 2 * n + b.toNat := congrFun (congrFun bit_eq_bitImpl b) n

@[simp, grind =]
theorem bit_inj (n m : Nat) (b d : Bool) : n.bit b = m.bit d ↔ n = m ∧ b = d := by
  fun_induction n.bit b generalizing m <;> grind [cases Bool, cases Nat]

theorem eq_of_bit_eq (n m : Nat) {b d : Bool} (h : n.bit b = bit d m) : n = m := by
  grind

theorem bool_eq_of_bit_eq (n m : Nat) {b d : Bool} (h : n.bit b = bit d m) : b = d := by
  grind

@[simp] theorem bit_eq_zero_iff {b n} : n.bit b = 0 ↔ n = 0 ∧ b = false := bit_inj n 0 b false
theorem bit_ne_zero_iff {b n} : n.bit b ≠ 0 ↔ n ≠ 0 ∨ b = true := by grind [bit_eq_zero_iff]

@[grind =>]
theorem ne_zero_of_bit_ne_zero {b n} (hn : n.bit b = 0) : n = 0 := by grind [bit_eq_zero_iff]

@[grind =>]
theorem bit_ne_zero_of_ne_zero {b n} (hn : n ≠ 0) : n.bit b ≠ 0 := by grind [bit_eq_zero_iff]

@[grind =>]
theorem bit_true_ne_zero {n} : bit true n ≠ 0 := by grind [bit_eq_zero_iff]

instance {b} {n : Nat} [NeZero n] : NeZero (n.bit b) := ⟨bit_ne_zero_of_ne_zero <| NeZero.ne _⟩

instance {n} : NeZero (bit true n) := ⟨bit_true_ne_zero⟩

@[grind =]
theorem bit_lt_bit (n m : Nat) (b d : Bool) : bit b n < bit d m ↔ n < m + ((!b) && d).toNat := by
  fun_induction n.bit b generalizing m <;> fun_cases m.bit d <;> grind [cases Bool]

@[grind =]
theorem bit_lt_bit_of_eq (n m : Nat) (b : Bool) : bit b n < bit b m ↔ n < m := by
  grind [cases Bool]

@[grind =]
theorem bit_le_bit_iff_eq {b n m} : bit b n ≤ bit b m ↔ n ≤ m := by grind [Nat.le_iff_lt_or_eq]

@[grind =]
theorem zero_lt_bit_iff {b k} : 0 < bit b k ↔ 0 < k ∨ b = true := by grind

@[simp]
theorem zero_lt_bit_false {k} : 0 < bit false k ↔ 0 < k := by grind

@[simp]
theorem zero_lt_bit_true {k} : 0 < bit true k := by grind

/-! ### divTwo, isOdd, bit -/

@[simp, grind =] theorem isOdd_bit {b} {n : Nat} : (n.bit b).isOdd = b := by
  fun_induction bit <;> grind [cases Bool]

@[simp, grind =] theorem isEven_bit {b} {n : Nat} : (n.bit b).isEven = !b := by grind

@[simp, grind =] theorem divTwo_bit {b} {n : Nat} : (n.bit b).divTwo = n := by
  fun_induction bit <;> grind [cases Bool]

@[simp, grind =] theorem bit_isOdd_divTwo {n : Nat} : n.divTwo.bit n.isOdd = n := by
  fun_induction divTwo <;> grind

theorem bit_isEven_divTwo {n : Nat} : n.divTwo.bit n.isEven = if n.isOdd then n - 1 else n + 1 := by
  fun_induction divTwo <;> grind

theorem ext_divTwo_isOdd {m n : Nat} (h0 : m.divTwo = n.divTwo) (h1 : m.isOdd = n.isOdd) : m = n :=
  m.bit_isOdd_divTwo.symm.trans (h0 ▸ h1 ▸ n.bit_isOdd_divTwo)

theorem ext_divTwo_isOdd_iff (n m : Nat) : n = m ↔ n.divTwo = m.divTwo ∧ n.isOdd = m.isOdd := by
  grind [ext_divTwo_isOdd]

theorem exists_bit (n : Nat) : ∃ b m, n = bit b m := ⟨n.isOdd, n.divTwo, n.bit_isOdd_divTwo.symm⟩

theorem exists_divTwo_isOdd (b : Bool) (n : Nat) : ∃ m : Nat, m.isOdd = b ∧ m.divTwo = n :=
  ⟨n.bit b, n.isOdd_bit, n.divTwo_bit⟩

theorem testBit_bit_zero {b} {n : Nat} : (n.bit b).testBit 0 = b := by grind [isOdd_val.symm]
theorem testBit_bit_add_one {b m} {n : Nat} : (n.bit b).testBit (m + 1) = n.testBit m := by
  grind [testBit_zero_eq_isOdd, testBit_add_one_eq_testBit_divTwo]

@[grind =]
theorem testBit_bit {b m} {n : Nat} : (n.bit b).testBit m =
    if m = 0 then b else n.testBit (m - 1) := by grind [cases Nat, testBit_add_two_left]

/-! ### isOddDivTwo -/

theorem isOddDivTwo_zero : isOddDivTwo 0 = (false, 0) := rfl
theorem isOddDivTwo_one : isOddDivTwo 1 = (true, 0) := rfl
theorem isOddDivTwo_add_two {n} : isOddDivTwo (n + 2) = (n.isOdd, n.divTwo + 1) := rfl

@[simp, grind =]
theorem isOddDivTwo_eq {n : Nat} : n.isOddDivTwo = (n.isOdd, n.divTwo) := rfl

theorem isOddDivTwo_succ {n : Nat} : isOddDivTwo (n + 1) =
    (isOddDivTwo n).map Bool.not (bif (isOddDivTwo n).1 then Nat.succ else id) := by
  simp [divTwo_add_one] <;> cases h : isOdd n <;> rfl

theorem leftInverse_isOddDivTwo_uncurry_bit : isOddDivTwo.LeftInverse bit.uncurry := by grind
theorem rightInverse_isOddDivTwo_uncurry_bit  : isOddDivTwo.RightInverse bit.uncurry := by grind

/-! ### divTwoRec -/

section

variable {motive : Nat → Sort u} {zero : motive 0} {one : motive 1}
  {add_two : ∀ n, motive (n.divTwo + 1) → motive (n + 2)}

@[simp, grind =] theorem divTwoRec_zero : Nat.divTwoRec zero one add_two 0 = zero := by
  rw [Nat.divTwoRec]
@[simp, grind =] theorem divTwoRec_one : Nat.divTwoRec zero one add_two 1 = one := by
  rw [Nat.divTwoRec]
@[simp, grind =] theorem divTwoRec_add_two {n} : Nat.divTwoRec zero one add_two (n + 2) =
    add_two n (Nat.divTwoRec zero one add_two (n.divTwo + 1)) := by rw [Nat.divTwoRec]

theorem divTwoRec_bit_zero {b} :
    Nat.divTwoRec (motive := motive) zero one add_two (Nat.bit b 0) =
    if h : b = true then h ▸ one else b.of_not_eq_true h ▸ zero := by grind

theorem divTwoRec_bit_add_two {b} {n : Nat} :
    Nat.divTwoRec (motive := motive) zero one add_two (n.bit b + 2) =
    add_two (n.bit b) (n.divTwo_bit.symm ▸ Nat.divTwoRec zero one add_two (n + 1)) := by grind

end

/-! ### bitElim -/

section

variable {α} {zero : α} {one : α} {bit : Bool → α → α}

@[simp, grind =] theorem bitElim_zero : Nat.bitElim zero one bit 0 = zero := divTwoRec_zero
@[simp, grind =] theorem bitElim_one : Nat.bitElim zero one bit 1 = one := divTwoRec_one
@[simp, grind =] theorem bitElim_add_two {n} : Nat.bitElim zero one bit (n + 2) =
    bit n.isOdd (Nat.bitElim zero one bit (n.divTwo + 1)) := divTwoRec_add_two

theorem bitElim_eq_divTwoRec : Nat.bitElim zero one bit =
    Nat.divTwoRec zero one (bit ∘ isOdd) := rfl

theorem bitElim_bit {b n} :
    Nat.bitElim zero one bit (n.bit b) = if n = 0 then bif b then one else zero else
    bit b (Nat.bitElim zero one bit n) := by grind [cases Nat]

theorem bitElim_add_one {n} :
    Nat.bitElim zero one bit (n + 1) = if n = 0 then one else
    bit n.isEven (Nat.bitElim zero one bit (n.divTwo + n.isOdd.toNat)) := by
  cases n with | zero => grind | succ n => cases n.isEven_or_isOdd <;> grind [divTwo_add_one]

end

theorem bitElim_zero_one_bit_apply (n : Nat) : Nat.bitElim 0 1 Nat.bit n = n := by
  induction n using Nat.divTwoRec <;> grind

theorem bitElim_zero_one_bit : Nat.bitElim 0 1 Nat.bit = id :=
  funext bitElim_zero_one_bit_apply

/-! ### bitElimFromZero -/

section

variable {α} {zero one : α} {bit : Bool → α → α}

@[simp] theorem bitElimFromZero_def :
    Nat.bitElimFromZero zero bit = Nat.bitElim zero (bit true zero) bit := by grind

theorem bitElimFromZero_add_one {n} :
    Nat.bitElimFromZero zero bit (n + 1) =
    bit n.isEven (Nat.bitElimFromZero zero bit (n.divTwo + n.isOdd.toNat)) := by
  cases n <;> grind [divTwo_add_one]

theorem bitElimFromZero_bit {b n} :
    Nat.bitElimFromZero zero bit (n.bit b) = bif !b && n == 0 then zero else
    bit b (Nat.bitElimFromZero zero bit n) := by cases n <;> grind

end

theorem bitElimFromZero_zero_bit_apply {n} : Nat.bitElimFromZero 0 Nat.bit n = n := by
  induction n using Nat.divTwoRec <;> grind

theorem bitElimFromZero_zero_one_bit : Nat.bitElimFromZero 0 Nat.bit = id :=
  funext bitElim_zero_one_bit_apply

/-! ### size -/

@[simp, grind =] theorem size_zero : size 0 = 0 := bitElim_zero
@[simp, grind =] theorem size_one : size 1 = 1 := bitElim_one
@[simp, grind =] theorem size_add_two {n} : size (n + 2) = size (n.divTwo + 1) + 1 :=
  bitElim_add_two

theorem size_add_one {n} : size (n + 1) =
    if n = 0 then 1 else size (n.divTwo + n.isOdd.toNat) + 1 := bitElim_add_one

theorem size_eq_zero_iff {n} : size n = 0 ↔ n = 0 := by grind [cases Nat]
theorem size_ne_zero_iff {n} : size n ≠ 0 ↔ n ≠ 0 := by grind [cases Nat]

@[grind =>]
theorem size_ne_zero_of_ne_zero {n} (hn : n ≠ 0) : size n ≠ 0 :=
  size_ne_zero_iff.mpr hn

instance {n} [NeZero n] : NeZero (size n) := ⟨size_ne_zero_of_ne_zero <| NeZero.ne _⟩

theorem size_succ_ne_zero {n} : size (n + 1) ≠ 0 := NeZero.ne _

@[grind =] theorem size_le_iff {m n : Nat} : size n ≤ m ↔ n < 2 ^ m := by
  induction n using Nat.divTwoRec generalizing m <;>
  cases m <;> grind [Nat.add_lt_iff_lt_sub_right]

@[grind =] theorem lt_size_iff {m n : Nat} : m < size n ↔ 2 ^ m ≤ n := by
  simp [← Nat.not_le, size_le_iff]

theorem lt_size_self {n : Nat} : n < 2 ^ size n := size_le_iff.mp n.size.le_refl

theorem size_eq_add_one_iff {m n : Nat} : size n = m + 1 ↔
    2 ^ m ≤ n ∧ n < 2 ^ (m + 1) := by rw [Nat.le_antisymm_iff]; grind

theorem size_eq_iff {m n : Nat} : size n = m ↔ n < 2 ^ m ∧ (m = 0 ∨ 2 ^ (m - 1) ≤ n) := by
  cases m
  · grind [size_eq_zero_iff]
  · grind [size_eq_add_one_iff]

@[grind =] theorem size_two_pow {n : Nat} : size (2 ^ n) = n + 1 :=
  size_eq_add_one_iff.mpr ⟨(2 ^ n).le_refl, Nat.pow_lt_pow_succ Nat.one_lt_two⟩

@[grind =]
theorem size_bit {b n} : size (n.bit b) = if n = 0 then b.toNat else size n + 1 :=
  bitElim_bit

theorem size_bit_zero {b} : size (bit b 0) = b.toNat := by grind

@[simp] theorem size_bit_true {n} : size (bit true n) = size n + 1 := by grind

theorem size_bit_of_ne_zero {b n} (hn : n ≠ 0) : size (n.bit b) = size n + 1 := by grind
@[simp] theorem size_bit_of_neZero {b n} [NeZero n] : size (n.bit b) = size n + 1 :=
  size_bit_of_ne_zero (NeZero.ne _)

theorem size_bit_add_two {b n} : size (n.bit b + 2) = size (n + 1) + 1 := by simp

/-! ### popcount -/

@[simp, grind =] theorem popcount_zero : popcount 0 = 0 := bitElim_zero
@[simp, grind =] theorem popcount_one : popcount 1 = 1 := bitElim_one
@[simp, grind =] theorem popcount_add_two {n} : popcount (n + 2) =
    popcount (n.divTwo + 1) + n.isOdd.toNat := bitElim_add_two

theorem popcount_add_one {n} : popcount (n + 1) = if n = 0 then 1 else
    popcount (n.divTwo + n.isOdd.toNat) + n.isEven.toNat := bitElim_add_one

@[simp, grind =]
theorem popcount_bit {b n} : popcount (n.bit b) = popcount n + b.toNat :=
  calc  _ = if n = 0 then b.toNat else popcount n + b.toNat := bitElim_bit
        _ = _ := by grind

theorem popcount_eq_zero_iff {n} : popcount n = 0 ↔ n = 0 := by
  induction n using Nat.divTwoRec <;> grind

theorem popcount_ne_zero_iff {n} : popcount n ≠ 0 ↔ n ≠ 0 := by
  grind [popcount_eq_zero_iff]

@[grind =>]
theorem popcount_ne_zero_of_ne_zero {n} (hn : n ≠ 0) : popcount n ≠ 0 :=
  popcount_ne_zero_iff.mpr hn

instance {n} [NeZero n] : NeZero (popcount n) := ⟨popcount_ne_zero_of_ne_zero <| NeZero.ne _⟩

theorem popcount_succ_ne_zero {n} : popcount (n + 1) ≠ 0 := NeZero.ne _

@[grind .] theorem popcount_le_size {n} : popcount n ≤ size n := by
  induction n using Nat.divTwoRec <;> grind

/-! ### bitsList -/

@[simp, grind =] theorem bitsList_zero : bitsList 0 = [] := by simp [bitsList]
@[simp, grind =] theorem bitsList_one : bitsList 1 = [true] := by simp [bitsList]
@[simp, grind =] theorem bitsList_add_two {n} : bitsList (n + 2) = n.isOdd ::
    bitsList (n.divTwo + 1) := by simp [bitsList]

theorem bitsList_add_one {n} : bitsList (n + 1) = if n = 0 then [true] else
  n.isEven :: bitsList (n.divTwo + n.isOdd.toNat) := bitElim_add_one

theorem head_bitsList {n : Nat} (hn : n.bitsList ≠ []) : n.bitsList.head hn = n.isOdd := by
  cases n <;> grind [cases Nat]

theorem head?_bitsList {n : Nat} : n.bitsList.head? = (Option.guard (· != 0) n).map isOdd := by
  grind [cases Nat]

@[grind =]
theorem bitsList_bit {b n} : bitsList (n.bit b) =
    if n = 0 then bif b then [true] else [] else b :: n.bitsList := bitElim_bit

@[grind =]
theorem bitsList_divTwo {n : Nat} : n.divTwo.bitsList = n.bitsList.tail := by grind [cases Nat]

theorem bitsList_bits_of_zero_imp_true {n b} (hn : n = 0 → b = true) :
    (n.bit b).bitsList = b :: n.bitsList := by grind

theorem bitsList_bit_zero {b} : bitsList (bit b 0) = bif b then [true] else [] := by grind

@[simp] theorem bitsList_bit_true {n} : bitsList (bit true n) = true :: bitsList n := by
  grind [cases Nat]

theorem bitsList_bit_of_ne_zero {b n} (hn : n ≠ 0) : bitsList (n.bit b) = b :: bitsList n := by
  grind

@[simp] theorem bitsList_bit_of_neZero {b n} [NeZero n] : bitsList (n.bit b) = b :: bitsList n :=
  bitsList_bit_of_ne_zero (NeZero.ne _)

theorem bitsList_bit_add_two {b n} : bitsList (n.bit b + 2) = b :: bitsList (n + 1) := by simp

@[simp] theorem bitsList_succ_ne_nil {n} : bitsList (n + 1) ≠ [] := by grind [cases Nat]

@[grind =] theorem bitsList_eq_nil_iff {n} : bitsList n = [] ↔ n = 0 := by grind [cases Nat]
theorem bitsList_ne_nil_iff {n} : bitsList n ≠ [] ↔ n ≠ 0 := by grind

@[grind =>] theorem bitsList_eq_nil_of_ne_zero {n} (hn : n ≠ 0) : bitsList n ≠ [] := by grind

@[simp]
theorem bitsList_eq_nil_of_neZero {n} [NeZero n] : bitsList n ≠ [] :=
  bitsList_eq_nil_of_ne_zero <| NeZero.ne _

@[simp, grind =]
theorem getElem_bitsList {n i} (hi : i < (bitsList n).length) : (bitsList n)[i] = n.testBit i := by
  induction n using Nat.divTwoRec generalizing i <;>
  grind [cases Nat, testBit_zero_eq_isOdd, testBit_add_one_eq_testBit_divTwo]

@[simp, grind =] theorem length_bitsList {n} : (bitsList n).length = size n := by
  induction n using Nat.divTwoRec <;> grind

theorem bitsList_eq_ofFn_testBit {n} : bitsList n = List.ofFn (n := n.size) (n.testBit ·) := by
  apply List.ext_getElem <;> simp

@[simp, grind =]
theorem getLast_bitsList {n} (hn : bitsList n ≠ []) : n.bitsList.getLast hn = true := by
  induction n using Nat.divTwoRec <;> grind

theorem getLast_bitsList_of_ne_zero {n} (hn : n ≠ 0) :
    n.bitsList.getLast (bitsList_eq_nil_of_ne_zero hn) = true := getLast_bitsList _

theorem getLast_bitsList_of_neZero {n : Nat} [NeZero n] :
    n.bitsList.getLast bitsList_eq_nil_of_neZero = true := getLast_bitsList _

theorem getLast_bitsList_add_one {n} : (n + 1).bitsList.getLast bitsList_succ_ne_nil = true :=
  getLast_bitsList _

theorem count_true_bitsList {n : Nat} : n.bitsList.count true = n.popcount := by
  induction n using Nat.divTwoRec <;> grind

theorem count_false_bitsList {n : Nat} : n.bitsList.count false = n.size - n.popcount := by
  apply Nat.eq_sub_of_add_eq
  simp only [List.count_eq_countP, ← count_true_bitsList, ← length_bitsList,
  List.length_eq_countP_add_countP (·), beq_false, beq_true]
  grind

/-! ### ofBitsList -/

@[simp, grind =] theorem ofBitsList_nil : ofBitsList [] = 0 := rfl
@[simp, grind =] theorem ofBitsList_cons {b bs} : ofBitsList (b :: bs) = bit b (ofBitsList bs) :=
  rfl

@[simp] theorem ofBitsList_eq_zero_iff {bs} : ofBitsList bs = 0 ↔ true ∉ bs := by
  induction bs <;> grind

@[grind .]
theorem ofBitsList_ne_zero_iff {bs} : ofBitsList bs ≠ 0 ↔ true ∈ bs := by simp

@[grind .]
theorem true_mem_of_ne_zero_ofBitsList {bs} (h : ofBitsList bs ≠ 0) : true ∈ bs := by simpa using h

@[grind .]
theorem true_mem_of_neZero_ofBitsList {bs} [NeZero (ofBitsList bs)] : true ∈ bs :=
  true_mem_of_ne_zero_ofBitsList (NeZero.ne _)

theorem ne_zero_ofBitsList_of_true_mem {bs} (h : true ∈ bs) : ofBitsList bs ≠ 0 := by simpa using h

theorem ofBitsList_replicate_false {n} : ofBitsList (List.replicate n false) = 0 := by
  induction n <;> grind [cases Bool]

theorem ofBitsList_replicate_true {n} : ofBitsList (List.replicate n true) = 2^n - 1 := by
  induction n <;> grind

theorem ofBitsList_lt_two_pow {bs} : ofBitsList bs < 2 ^ bs.length := by
  induction bs <;> grind [cases Bool]

@[grind =] theorem testBit_ofBitsList (bs : List Bool) (i : Nat) :
    (ofBitsList bs).testBit i = bs[i]?.getD false := by induction bs generalizing i <;> grind

@[simp] theorem testBit_ofBitsList_lt (bs : List Bool) (i : Nat) (h : i < bs.length) :
    (ofBitsList bs).testBit i = bs[i] := by grind

@[simp] theorem testBit_ofBitsList_ge (bs : List Bool) (i : Nat) (h : bs.length ≤ i) :
    (ofBitsList bs).testBit i = false := by grind

/-! ### bitsList, ofBitsList -/

@[grind =]
theorem ofBitsList_bitsList (n : Nat) : ofBitsList (bitsList n) = n := by
  induction n using Nat.divTwoRec <;> grind

theorem leftInverse_ofBitsList_bitsList : ofBitsList.LeftInverse bitsList :=
  ofBitsList_bitsList

theorem injective_bitsList : bitsList.Injective :=
  leftInverse_ofBitsList_bitsList.injective

theorem eq_of_bitsList_eq {m n} (hmn : bitsList m = bitsList n) : m = n := injective_bitsList hmn

theorem bitsList_inj {m n} : bitsList m = bitsList n ↔ m = n := by grind [eq_of_bitsList_eq]

@[grind =] theorem bitsList_ofBitsList_of_forall_getLast_eq_true {bs : List Bool}
    (hbs : (hbs : bs ≠ []) → bs.getLast hbs = true) : bitsList (ofBitsList bs) = bs := by
  induction bs <;> grind

theorem bitsList_ofBitsList_nil : bitsList (ofBitsList []) = [] := by grind

theorem bitsList_ofBitsList_concat_true {bs : List Bool} :
    bitsList (ofBitsList (bs ++ [true])) = bs ++ [true] := by grind

theorem bitsList_ofBitsList_of_getLast_eq_true {bs : List Bool} (hbs₁ : bs ≠ [])
    (hbs₂ : bs.getLast hbs₁ = true) : bitsList (ofBitsList bs) = bs := by grind

/-! ### leastBitsList -/

@[simp, grind =] theorem leastBitsList_zero : leastBitsList 0 = none := by simp [leastBitsList]
@[grind =] theorem leastBitsList_one : leastBitsList 1 = some [] := by simp [leastBitsList]
@[simp, grind =] theorem leastBitsList_add_two {n} : leastBitsList (n + 2) =
    (n.divTwo + 1).leastBitsList.map (n.isOdd :: ·) := by simp [leastBitsList]

@[grind =]
theorem leastBitsList_eq {n} :
    leastBitsList n = if n = 0 then none else some (bitsList n).dropLast := by
  induction n using Nat.divTwoRec <;> grind [List.dropLast_cons_of_ne_nil]

theorem leastBitsList_eq_of_ne_zero {n} (hn : n ≠ 0) :
    leastBitsList n = some (bitsList n).dropLast := by grind

@[simp]
theorem leastBitsList_eq_of_neZero {n} [NeZero n] :
    leastBitsList n = some n.bitsList.dropLast :=
  leastBitsList_eq_of_ne_zero (NeZero.ne _)

@[simp] theorem leastBitsList_eq_none_iff {n} : leastBitsList n = none ↔ n = 0 := by grind

theorem leastBitsList_ne_none_iff {n} : leastBitsList n ≠ none ↔ n ≠ 0 := by grind

theorem leastBitsList_succ_ne_none {n} : leastBitsList (n + 1) ≠ none := by grind

theorem leastBitsList_add_one {n} : leastBitsList (n + 1) = some (bitsList (n + 1)).dropLast := by
  grind

theorem bitsList_eq {n} : bitsList n = (leastBitsList n).elim [] (· ++ [true]) := by
  grind [List.dropLast_concat_getLast]

@[grind =]
theorem leastBitsList_bit {b n} : leastBitsList (n.bit b) =
    if n = 0 then bif b then some [] else none else some (b :: (bitsList n).dropLast) := by
  grind [cases Nat]

theorem leastBitsList_bit_zero {b} :
    leastBitsList (bit b 0) = bif b then some [] else none := by grind

theorem leastBitsList_bit_true {n} : leastBitsList (bit true n) =
    if n = 0 then some [] else (leastBitsList n).map (true :: ·) := by grind

/-! ### ofLeastBitsList -/

@[simp, grind =] theorem ofLeastBitsList_none : ofLeastBitsList none = 0 := rfl
@[simp, grind =] theorem ofLeastBitsList_some_nil : ofLeastBitsList (some []) = 1 := rfl
@[simp, grind =] theorem ofLeastBitsList_some_cons :
    ofLeastBitsList (some (b :: bs)) = bit b (ofLeastBitsList (some bs)) := by
  grind [ofLeastBitsList]

@[grind =]
theorem ofLeastBitsList_eq {oxs} : ofLeastBitsList oxs =
    oxs.elim 0 (ofBitsList ∘ (· ++ [true])) := by
  cases oxs with | none => grind | some bs => induction bs <;> grind

@[simp]
theorem ofLeastBitsList_eq_zero_iff {oxs} : ofLeastBitsList oxs = 0 ↔ oxs = none := by
  grind [cases Option]

theorem ofLeastBitsList_ne_zero_iff {oxs} : ofLeastBitsList oxs ≠ 0 ↔ oxs ≠ none := by simp

theorem ofLeastBitsList_some_ne_zero {bs} : ofLeastBitsList (some bs) ≠ 0 := by simp

instance : NeZero (ofLeastBitsList (some bs)) := ⟨ofLeastBitsList_some_ne_zero⟩

/-! ### leastBitsList, ofLeastBitsList -/

theorem ofLeastBitsList_leastBitsList (n) : ofLeastBitsList (leastBitsList n) = n := by
  grind [List.dropLast_concat_getLast]

theorem leastBitsList_ofLeastBitsList (oxs : Option (List Bool)) :
    leastBitsList (ofLeastBitsList oxs) = oxs := by grind [cases Option]

theorem leftInverse_ofLeastBitsList_leastBitsList :
    ofLeastBitsList.LeftInverse leastBitsList := ofLeastBitsList_leastBitsList

theorem injective_leastBitsList : leastBitsList.Injective :=
  leftInverse_ofLeastBitsList_leastBitsList.injective

theorem rightInverse_ofLeastBitsList_leastBitsList :
    ofLeastBitsList.RightInverse leastBitsList := leastBitsList_ofLeastBitsList

theorem injective_ofLeastBitsList : ofLeastBitsList.Injective :=
  rightInverse_ofLeastBitsList_leastBitsList.injective

theorem leastBitsList_inj : leastBitsList n = leastBitsList m ↔ n = m :=
  injective_leastBitsList.eq_iff

theorem ofLeastBitsList_inj : ofLeastBitsList oxs = ofLeastBitsList oys ↔ oxs = oys :=
  injective_ofLeastBitsList.eq_iff

/- ## bitUnary -/

section

variable {f : Bool → Bool}

@[simp, grind =] theorem bitUnary_zero : bitUnary f 0 = 0 := bitElim_zero
@[simp, grind =] theorem bitUnary_one : bitUnary f 1 = (f true).toNat := bitElim_one
@[simp, grind =] theorem bitUnary_add_two {n} :
    bitUnary f (n + 2) = bit (f n.isOdd) (bitUnary f (n.divTwo + 1)) := bitElim_add_two

theorem bitUnary_add_one {n} :
    bitUnary f (n + 1) = bit (f n.isEven) (bitUnary f (n.divTwo + n.isOdd.toNat)) :=
  bitElimFromZero_add_one

end

@[simp, grind =]
theorem testBit_bitUnary {n i} : (bitUnary f n).testBit i =
    (decide (i < n.size) && f (n.testBit i)) := by
  induction n using Nat.divTwoRec generalizing i <;> cases i <;>
  grind [testBit_zero_eq_isOdd, testBit_add_one_eq_testBit_divTwo]

/- ## bitBinary -/

section

variable {f : Bool → Bool → Bool}

@[simp, grind =] theorem bitBinary_zero_left {n} :
    bitBinary f 0 n = bitUnary (f false) n := congrFun bitElim_zero n
@[simp, grind =] theorem bitBinary_one_left {n} :
    bitBinary f 1 n = bit (f true n.isOdd) (bitUnary (f false) n.divTwo) :=
  congrFun bitElim_one n
@[simp, grind =] theorem bitBinary_add_two_left {m n} :
    bitBinary f (m + 2) n = bit (f m.isOdd n.isOdd) (bitBinary f (m.divTwo + 1) n.divTwo) :=
  congrFun bitElim_add_two n

theorem bitBinary_add_one_left {m n} :
    bitBinary f (m + 1) n = bit (f m.isEven n.isOdd)
    (bitBinary f (m.divTwo + m.isOdd.toNat) n.divTwo) :=
  congrFun bitElimFromZero_add_one n

theorem bitBinary_zero_zero : bitBinary f 0 0 = 0 := by simp
theorem bitBinary_zero_one : bitBinary f 0 1 = (f false true).toNat := by simp
theorem bitBinary_zero_add_two {n} :
    bitBinary f 0 (n + 2) = bit (f false n.isOdd) (bitUnary (f false) (n.divTwo + 1)) := by simp

theorem bitBinary_one_zero : bitBinary f 1 0 = (f true false).toNat := by simp
theorem bitBinary_one_one : bitBinary f 1 1 = (f true true).toNat := by simp
theorem bitBinary_one_add_two {n} :
    bitBinary f 1 (n + 2) = bit (f true n.isOdd) (bitUnary (f false) (n.divTwo + 1)) := by simp

theorem bitBinary_add_two_add_two {m n} :
    bitBinary f (m + 2) (n + 2)
      = bit (f m.isOdd n.isOdd) (bitBinary f (m.divTwo + 1) (n.divTwo + 1)) := by simp

@[simp, grind =] theorem bitBinary_add_two_right {m n} :
    bitBinary f m (n + 2)
      = bit (f m.isOdd n.isOdd) (bitBinary f m.divTwo (n.divTwo + 1)) := by
  cases m using Nat.divTwoRec <;> simp

@[simp, grind =] theorem bitBinary_zero_right {n} :
    bitBinary f n 0 = bitUnary (f · false) n := by induction n using Nat.divTwoRec <;> grind
@[simp, grind =] theorem bitBinary_one_right {n} :
    bitBinary f n 1 = bit (f n.isOdd true) (bitUnary (f · false) n.divTwo) := by
  cases n using Nat.divTwoRec <;> simp

theorem bitBinary_add_two_zero {n} :
    bitBinary f (n + 2) 0 = bit (f n.isOdd false) (bitUnary (f · false) (n.divTwo + 1)) := by simp
theorem bitBinary_add_two_one {n} :
    bitBinary f (n + 2) 1 = bit (f n.isOdd true) (bitUnary (f · false) (n.divTwo + 1)) := by simp

theorem bitBinary_flip (f : Bool → Bool → Bool) {m n : Nat} :
    bitBinary (flip f) m n = bitBinary f n m := by
  unfold flip; induction n using Nat.divTwoRec generalizing m <;> grind

attribute [-grind] testBit_eq_decide_div_mod_eq in
@[simp, grind =]
theorem testBit_bitBinary {n m i} : (bitBinary f m n).testBit i =
    ((decide (i < m.size) || decide (i < n.size)) && f (m.testBit i) (n.testBit i)) := by
  induction n using Nat.divTwoRec generalizing i m <;> cases m using Nat.divTwoRec <;> cases i <;>
  grind [testBit_zero_eq_isOdd, testBit_add_one_eq_testBit_divTwo]

end

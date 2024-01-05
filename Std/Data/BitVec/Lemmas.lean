import Std.Data.Bool
import Std.Data.BitVec.Basic
import Std.Data.Nat.Lemmas

import Std.Tactic.Simpa

namespace Std.BitVec

/-- Prove equality of bitvectors in terms of nat operations. -/
theorem eq_of_toNat_eq {n} : ∀ {i j : BitVec n}, i.toNat = j.toNat → i = j
  | ⟨_, _⟩, ⟨_, _⟩, rfl => rfl

theorem toNat_eq (x y : BitVec n) : x = y ↔ x.toNat = y.toNat :=
  Iff.intro (congrArg BitVec.toNat) eq_of_toNat_eq

theorem testBit_toNat (x : BitVec w) : x.toNat.testBit i = x.getLsb i := rfl

@[simp] theorem getLsb_ge (x : BitVec w) (i : Nat) (ge : i ≥ w) : getLsb x i = false := by
  let ⟨x, x_lt⟩ := x
  apply Nat.testBit_lt_two
  apply Nat.lt_of_lt_of_le x_lt
  apply Nat.pow_le_pow_of_le_right (by trivial : 0 < 2) ge

theorem eq_of_getLsb_eq {x y : BitVec w}
    (pred : ∀(i : Fin w), x.getLsb i.val = y.getLsb i.val) : x = y := by
  apply eq_of_toNat_eq
  apply Nat.eq_of_testBit_eq
  intro i
  if i_lt : i < w then
    exact pred ⟨i, i_lt⟩
  else
    have p : i ≥ w := Nat.le_of_not_gt i_lt
    simp [testBit_toNat, getLsb_ge _ _ p]

theorem eq_of_getMsb_eq {x y : BitVec w}
    (pred : ∀(i : Fin w), x.getMsb i = y.getMsb i.val) : x = y := by
  simp only [getMsb] at pred
  apply eq_of_getLsb_eq
  intro ⟨i, i_lt⟩
  if w_zero : w = 0 then
    simp [w_zero]
  else
    have w_pos := Nat.pos_of_ne_zero w_zero
    have r : i ≤ w - 1 := by
      simp [Nat.le_sub_iff_add_le w_pos, Nat.add_succ]
      exact i_lt
    have q_lt : w - 1 - i < w := by
      simp only [Nat.sub_sub]
      apply Nat.sub_lt w_pos
      simp [Nat.succ_add]
    have q := pred ⟨w - 1 - i, q_lt⟩
    simpa [q_lt, Nat.sub_sub_self, r] using q

@[simp] theorem toNat_ofBool (b : Bool) : (ofBool b).toNat = b.toNat := by
  cases b <;> rfl

@[simp] theorem toNat_ofFin (x : Fin (2^n)) : (BitVec.ofFin x).toNat = x.val := rfl

theorem toNat_ofNat (x w : Nat) : (BitVec.ofNat w x).toNat = x % 2^w := by
  simp [BitVec.toNat, BitVec.ofNat, Fin.ofNat']

@[simp] theorem toNat_zero (n : Nat) : (0#n).toNat = 0 := by trivial

private theorem lt_two_pow_of_le {x m n : Nat} (lt : x < 2 ^ m) (le : m ≤ n) : x < 2 ^ n :=
  Nat.lt_of_lt_of_le lt (Nat.pow_le_pow_of_le_right (by trivial : 0 < 2) le)

@[simp] theorem ofNat_toNat (m : Nat) (x : BitVec n) : (BitVec.ofNat m x.toNat) = truncate m x := by
  let ⟨x, lt_n⟩ := x
  unfold truncate
  unfold zeroExtend
  if h : n ≤ m then
    unfold zeroExtend'
    have lt_m : x < 2 ^ m := lt_two_pow_of_le lt_n h
    simp [h, lt_m, Nat.mod_eq_of_lt, BitVec.toNat, BitVec.ofNat, Fin.ofNat']
  else
    simp [h]

theorem toNat_append (x : BitVec m) (y : BitVec n) : (x ++ y).toNat = x.toNat <<< n ||| y.toNat :=
  rfl

@[simp] theorem toNat_cast (e : m = n) (x : BitVec m) : (cast e x).toNat = x.toNat := rfl

theorem toNat_cons (b : Bool) (x : BitVec w) : (cons b x).toNat = (b.toNat <<< w) ||| x.toNat := by
  let ⟨x, _⟩ := x
  simp [cons, toNat_append, toNat_ofBool]

/-! ### cons -/

theorem getLsb_cons (b : Bool) {n} (x : BitVec n) (i : Nat) :
    getLsb (cons b x) i = if i = n then b else getLsb x i := by
  simp only [getLsb, toNat_cons, Nat.testBit_or]
  rw [Nat.testBit_shiftLeft]
  rcases Nat.lt_trichotomy i n with i_lt_n | i_eq_n | n_lt_i
  · have i_ge_n := Nat.not_le_of_gt i_lt_n
    have not_eq := Nat.ne_of_lt i_lt_n
    simp [i_ge_n, not_eq]
  · simp [i_eq_n, testBit_toNat]
    cases b <;> trivial
  · have i_ge_n : n ≤ i := Nat.le_of_lt n_lt_i
    have not_eq := Nat.ne_of_gt n_lt_i
    have neq_zero : i - n ≠ 0 := Nat.sub_ne_zero_of_lt n_lt_i
    simp [i_ge_n, not_eq, Nat.testBit_bool_to_nat, neq_zero]

/-! ### zeroExtend and truncate -/

@[simp] theorem toNat_zeroExtend' {m n : Nat} (p : m ≤ n) (x : BitVec m) :
    (zeroExtend' p x).toNat = x.toNat := by
  unfold zeroExtend'
  simp [p, x.isLt, Nat.mod_eq_of_lt]

theorem toNat_zeroExtend (i : Nat) (x : BitVec n) :
    BitVec.toNat (zeroExtend i x) = x.toNat % 2^i := by
  let ⟨x, lt_n⟩ := x
  simp only [zeroExtend]
  if n_le_i : n ≤ i then
    have x_lt_two_i : x < 2 ^ i := lt_two_pow_of_le lt_n n_le_i
    simp [n_le_i, Nat.mod_eq_of_lt, x_lt_two_i]
  else
    simp [n_le_i, toNat_ofNat]

@[simp] theorem zeroExtend_eq (x : BitVec n) : zeroExtend n x = x := by
  apply eq_of_toNat_eq
  let ⟨x, lt_n⟩ := x
  simp [truncate, zeroExtend]

@[simp] theorem zeroExtend_zero (m n : Nat) : zeroExtend m (0#n) = 0#m := by
  apply eq_of_toNat_eq
  simp [toNat_zeroExtend]

@[simp] theorem truncate_eq (x : BitVec n) : truncate n x = x := zeroExtend_eq x

@[simp] theorem toNat_truncate (x : BitVec n) : (truncate i x).toNat = x.toNat % 2^i :=
  toNat_zeroExtend i x

theorem getLsb_zeroExtend' (ge : m ≥ n) (x : BitVec n) (i : Nat) :
    getLsb (zeroExtend' ge x) i = getLsb x i := by
  simp [getLsb, toNat_zeroExtend']

theorem getLsb_zeroExtend (m : Nat) (x : BitVec n) (i : Nat) :
    getLsb (zeroExtend m x) i = (decide (i < m) && getLsb x i) := by
  simp [getLsb, toNat_zeroExtend, Nat.testBit_mod_two_pow]

theorem getLsb_truncate (m : Nat) (x : BitVec n) (i : Nat) :
    getLsb (truncate m x) i = (decide (i < m) && getLsb x i) :=
  getLsb_zeroExtend m x i

theorem truncate_succ (x : BitVec w) :
    truncate (i+1) x = cons (getLsb x i) (truncate i x) := by
  apply eq_of_getLsb_eq
  intro j
  simp only [getLsb_truncate, getLsb_cons, j.isLt, decide_True, Bool.true_and]
  if j_eq : j.val = i then
    simp [j_eq]
  else
    have j_lt : j.val < i := Nat.lt_of_le_of_ne (Nat.le_of_succ_le_succ j.isLt) j_eq
    simp [j_eq, j_lt]

/-! ### add -/

/--
Definition of bitvector addition as a nat.
-/
theorem toNat_add (x y : BitVec w) : (x + y).toNat = (x.toNat + y.toNat) % 2^w := by rfl

@[simp] theorem add_zero (x : BitVec n) : x + (0#n) = x := by
  apply eq_of_toNat_eq
  simp [toNat_add, isLt, Nat.mod_eq_of_lt]

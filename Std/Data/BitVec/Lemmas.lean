import Std.Data.Bool
import Std.Data.BitVec.Basic
import Std.Data.Fin.Lemmas
import Std.Data.Nat.Lemmas

import Std.Tactic.Ext
import Std.Tactic.Simpa
import Std.Tactic.Omega

namespace Std.BitVec

/-- Prove equality of bitvectors in terms of nat operations. -/
theorem eq_of_toNat_eq {n} : ∀ {i j : BitVec n}, i.toNat = j.toNat → i = j
  | ⟨_, _⟩, ⟨_, _⟩, rfl => rfl

theorem zero_is_unique (x : BitVec 0) : x = 0#0 := by
  let ⟨i, lt⟩ := x
  have p : i < 1 := lt
  have q : i = 0 := by omega
  simp [q]
  rfl

@[simp] theorem val_toFin (x : BitVec w) : x.toFin.val = x.toNat := rfl

theorem toNat_eq (x y : BitVec n) : x = y ↔ x.toNat = y.toNat :=
  Iff.intro (congrArg BitVec.toNat) eq_of_toNat_eq

theorem toNat_lt (x : BitVec n) : x.toNat < 2^n := x.toFin.2

theorem testBit_toNat (x : BitVec w) : x.toNat.testBit i = x.getLsb i := rfl

@[simp] theorem getLsb_ofFin (x : Fin (2^n)) (i : Nat) :
  getLsb (BitVec.ofFin x) i = x.val.testBit i := rfl

@[simp] theorem getLsb_ge (x : BitVec w) (i : Nat) (ge : i ≥ w) : getLsb x i = false := by
  let ⟨x, x_lt⟩ := x
  simp
  apply Nat.testBit_lt_two
  have p : 2^w ≤ 2^i := Nat.pow_le_pow_of_le_right (by omega) ge
  omega

-- We choose `eq_of_getLsb_eq` as the `@[ext]` theorem for `BitVec`
-- somewhat arbitrarily over `eq_of_getMsg_eq`.
@[ext] theorem eq_of_getLsb_eq {x y : BitVec w}
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

@[simp] theorem toNat_ofNat (x w : Nat) : (x#w).toNat = x % 2^w := by
  simp [BitVec.toNat, BitVec.ofNat, Fin.ofNat']

@[simp] theorem getLsb_ofNat (n : Nat) (x : Nat) (i : Nat) :
  getLsb (x#n) i = (i < n && x.testBit i) := by
  simp [getLsb, BitVec.ofNat, Fin.val_ofNat']

@[deprecated toNat_ofNat] theorem toNat_zero (n : Nat) : (0#n).toNat = 0 := by trivial

@[simp] theorem toNat_mod_cancel (x : BitVec n) : x.toNat % (2^n) = x.toNat :=
  Nat.mod_eq_of_lt x.isLt

private theorem lt_two_pow_of_le {x m n : Nat} (lt : x < 2 ^ m) (le : m ≤ n) : x < 2 ^ n :=
  Nat.lt_of_lt_of_le lt (Nat.pow_le_pow_of_le_right (by trivial : 0 < 2) le)

@[simp] theorem ofNat_toNat (m : Nat) (x : BitVec n) : x.toNat#m = truncate m x := by
  let ⟨x, lt_n⟩ := x
  unfold truncate
  unfold zeroExtend
  if h : n ≤ m then
    unfold zeroExtend'
    have lt_m : x < 2 ^ m := lt_two_pow_of_le lt_n h
    simp [h, lt_m, Nat.mod_eq_of_lt, BitVec.toNat, BitVec.ofNat, Fin.ofNat']
  else
    simp [h]

/-! ### cast -/

@[simp] theorem toNat_cast (e : m = n) (x : BitVec m) : (cast e x).toNat = x.toNat := rfl

@[simp] theorem getLsb_cast : (cast h v).getLsb i = v.getLsb i := by
  cases h
  simp

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

@[simp] theorem getLsb_zeroExtend' (ge : m ≥ n) (x : BitVec n) (i : Nat) :
    getLsb (zeroExtend' ge x) i = getLsb x i := by
  simp [getLsb, toNat_zeroExtend']

@[simp] theorem getLsb_zeroExtend (m : Nat) (x : BitVec n) (i : Nat) :
    getLsb (zeroExtend m x) i = (decide (i < m) && getLsb x i) := by
  simp [getLsb, toNat_zeroExtend, Nat.testBit_mod_two_pow]

@[simp] theorem getLsb_truncate (m : Nat) (x : BitVec n) (i : Nat) :
    getLsb (truncate m x) i = (decide (i < m) && getLsb x i) :=
  getLsb_zeroExtend m x i

/-! ## extractLsb -/

@[simp]
protected theorem extractLsb_ofFin {n} (x : Fin (2^n)) (hi lo : Nat) :
  extractLsb hi lo (@BitVec.ofFin n x) = .ofNat (hi-lo+1) (x.val >>> lo) := rfl

@[simp]
protected theorem extractLsb_ofNat (x n : Nat) (hi lo : Nat) :
  extractLsb hi lo x#n = .ofNat (hi - lo + 1) ((x % 2^n) >>> lo) := by
  apply eq_of_getLsb_eq
  intro ⟨i, _lt⟩
  simp [BitVec.ofNat]

@[simp] theorem extractLsb'_toNat (s m : Nat) (x : BitVec n) :
  (extractLsb' s m x).toNat = (x.toNat >>> s) % 2^m := rfl

@[simp] theorem extractLsb_toNat (hi lo : Nat) (x : BitVec n) :
  (extractLsb hi lo x).toNat = (x.toNat >>> lo) % 2^(hi-lo+1) := rfl

@[simp] theorem getLsb_extract (hi lo : Nat) (x : BitVec n) (i : Nat) :
    getLsb (extractLsb hi lo x) i = (i ≤ (hi-lo) && getLsb x (lo+i)) := by
  unfold getLsb
  simp [Nat.lt_succ]

/-! ### or -/

@[simp] theorem toNat_or {x y : BitVec v} :
    BitVec.toNat (x ||| y) = BitVec.toNat x ||| BitVec.toNat y := rfl

@[simp] theorem getLsb_or {x y : BitVec v} : (x ||| y).getLsb i = (x.getLsb i || y.getLsb i) := by
  rw [← testBit_toNat, getLsb, getLsb]
  simp

/-! ### shiftLeft -/

@[simp] theorem toNat_shiftLeft {x : BitVec v} :
    BitVec.toNat (x <<< n) = BitVec.toNat x <<< n % 2^v :=
  BitVec.toNat_ofNat _ _

@[simp] theorem getLsb_shiftLeft (x : BitVec m) (n) :
    getLsb (x <<< n) i = (decide (i < m) && !decide (i < n) && getLsb x (i - n)) := by
  rw [← testBit_toNat, getLsb]
  simp only [toNat_shiftLeft, Nat.testBit_mod_two_pow, Nat.testBit_shiftLeft, ge_iff_le]
  -- This step could be a case bashing tactic.
  cases h₁ : decide (i < m) <;> cases h₂ : decide (n ≤ i) <;> cases h₃ : decide (i < n)
  all_goals { simp_all <;> omega }

theorem shiftLeftZeroExtend_eq {x : BitVec w} :
    shiftLeftZeroExtend x n = zeroExtend (w+n) x <<< n := by
  apply eq_of_toNat_eq
  rw [shiftLeftZeroExtend, zeroExtend]
  split
  · simp
    rw [Nat.mod_eq_of_lt]
    rw [Nat.shiftLeft_eq, Nat.pow_add]
    exact Nat.mul_lt_mul_of_pos_right (BitVec.toNat_lt x) (Nat.pow_two_pos _)
  · omega

@[simp] theorem getLsb_shiftLeftZeroExtend (x : BitVec m) (n : Nat) :
    getLsb (shiftLeftZeroExtend x n) i = ((! decide (i < n)) && getLsb x (i - n)) := by
  rw [shiftLeftZeroExtend_eq]
  simp only [getLsb_shiftLeft, getLsb_zeroExtend]
  cases h₁ : decide (i < n) <;> cases h₂ : decide (i - n < m + n) <;> cases h₃ : decide (i < m + n)
    <;> simp_all
    <;> (rw [getLsb_ge]; omega)

/-! ### ushiftRight -/

@[simp] theorem toNat_ushiftRight (x : BitVec n) (i : Nat) :
    (x >>> i).toNat = x.toNat >>> i := rfl

@[simp] theorem getLsb_ushiftRight (x : BitVec n) (i j : Nat) :
    getLsb (x >>> i) j = getLsb x (i+j) := by
  unfold getLsb ; simp

/-! ### append -/

theorem append_def (x : BitVec v) (y : BitVec w) :
    x ++ y = (shiftLeftZeroExtend x w ||| zeroExtend' (Nat.le_add_left w v) y) := rfl

@[simp] theorem toNat_append (x : BitVec m) (y : BitVec n) :
    (x ++ y).toNat = x.toNat <<< n ||| y.toNat :=
  rfl

@[simp] theorem getLsb_append {v : BitVec n} {w : BitVec m} :
    getLsb (v ++ w) i = bif i < m then getLsb w i else getLsb v (i - m) := by
  simp [append_def]
  by_cases h : i < m
  · simp [h]
  · simp [h]; simp_all

/-! ### cons -/

@[simp] theorem toNat_cons (b : Bool) (x : BitVec w) :
    (cons b x).toNat = (b.toNat <<< w) ||| x.toNat := by
  let ⟨x, _⟩ := x
  simp [cons, toNat_append, toNat_ofBool]

@[simp] theorem getLsb_cons (b : Bool) {n} (x : BitVec n) (i : Nat) :
    getLsb (cons b x) i = if i = n then b else getLsb x i := by
  simp only [getLsb, toNat_cons, Nat.testBit_or]
  rw [Nat.testBit_shiftLeft]
  rcases Nat.lt_trichotomy i n with i_lt_n | i_eq_n | n_lt_i
  · have p1 : ¬(n ≤ i) := by omega
    have p2 : i ≠ n := by omega
    simp [p1, p2]
  · simp [i_eq_n, testBit_toNat]
    cases b <;> trivial
  · have p1 : n ≤ i := by omega
    have p2 : i ≠ n := by omega
    have p3 : i - n ≠ 0 := by omega
    simp [p1, p2, p3, Nat.testBit_bool_to_nat]

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

theorem add_def {n} (x y : BitVec n) : x + y = .ofNat n (x.toNat + y.toNat) := rfl

/--
Definition of bitvector addition as a nat.
-/
@[simp] theorem toNat_add (x y : BitVec w) : (x + y).toNat = (x.toNat + y.toNat) % 2^w := rfl
@[simp] theorem ofFin_add (x : Fin (2^n)) (y : BitVec n) :
  .ofFin x + y = .ofFin (x + y.toFin) := rfl
@[simp] theorem add_ofFin (x : BitVec n) (y : Fin (2^n)) :
  x + .ofFin y = .ofFin (x.toFin + y) := rfl
@[simp] theorem ofNat_add_ofNat {n} (x y : Nat) : x#n + y#n = (x + y)#n := by
  apply eq_of_toNat_eq ; simp [BitVec.ofNat]

protected theorem add_assoc (x y z : BitVec n) : x + y + z = x + (y + z) := by
  apply eq_of_toNat_eq ; simp [Nat.add_assoc]

protected theorem add_comm (x y : BitVec n) : x + y = y + x := by
  simp [add_def, Nat.add_comm]

@[simp] protected theorem add_zero (x : BitVec n) : x + 0#n = x := by simp [add_def]

@[simp] protected theorem zero_add (x : BitVec n) : 0#n + x = x := by simp [add_def]


/-! ### sub/neg -/

theorem sub_def {n} (x y : BitVec n) : x - y = .ofNat n (x.toNat + (2^n - y.toNat)) := by rfl

@[simp] theorem sub_toNat {n} (x y : BitVec n) :
  (x - y).toNat = ((x.toNat + (2^n - y.toNat)) % 2^n) := rfl

@[simp] theorem ofFin_sub (x : Fin (2^n)) (y : BitVec n) : .ofFin x - y = .ofFin (x - y.toFin) :=
  rfl
@[simp] theorem sub_ofFin (x : BitVec n) (y : Fin (2^n)) : x - .ofFin y = .ofFin (x.toFin - y) :=
  rfl
@[simp] theorem ofNat_sub_ofNat {n} (x y : Nat) : x#n - y#n = .ofNat n (x + (2^n - y % 2^n)) := by
  apply eq_of_toNat_eq ; simp [BitVec.ofNat]

@[simp] protected theorem sub_zero (x : BitVec n) : x - (0#n) = x := by apply eq_of_toNat_eq ; simp

@[simp] protected theorem sub_self (x : BitVec n) : x - x = 0#n := by
  apply eq_of_toNat_eq
  simp only [sub_toNat]
  rw [Nat.add_sub_of_le]
  · simp
  · exact Nat.le_of_lt x.isLt

@[simp] theorem neg_toNat (x : BitVec n) : (- x).toNat = (2^n - x.toNat) % 2^n := by
  simp [Neg.neg, BitVec.neg]

theorem sub_toAdd {n} (x y : BitVec n) : x - y = x + - y := by
  apply eq_of_toNat_eq
  simp

@[simp] theorem neg_zero (n:Nat) : -0#n = 0#n := by apply eq_of_toNat_eq ; simp

/-! ### le and lt -/

theorem le_def (x y : BitVec n) :
  x ≤ y ↔ x.toNat ≤ y.toNat := Iff.rfl

@[simp] theorem le_ofFin (x : BitVec n) (y : Fin (2^n)) :
  x ≤ BitVec.ofFin y ↔ x.toFin ≤ y := Iff.rfl
@[simp] theorem ofFin_le (x : Fin (2^n)) (y : BitVec n) :
  BitVec.ofFin x ≤ y ↔ x ≤ y.toFin := Iff.rfl
@[simp] theorem ofNat_le_ofNat {n} (x y : Nat) : (x#n) ≤ (y#n) ↔ x % 2^n ≤ y % 2^n := by
  simp [le_def]

theorem lt_def (x y : BitVec n) :
  x < y ↔ x.toNat < y.toNat := Iff.rfl

@[simp] theorem lt_ofFin (x : BitVec n) (y : Fin (2^n)) :
  x < BitVec.ofFin y ↔ x.toFin < y := Iff.rfl
@[simp] theorem ofFin_lt (x : Fin (2^n)) (y : BitVec n) :
  BitVec.ofFin x < y ↔ x < y.toFin := Iff.rfl
@[simp] theorem ofNat_lt_ofNat {n} (x y : Nat) : (x#n) < (y#n) ↔ x % 2^n < y % 2^n := by
  simp [lt_def]

protected theorem lt_of_le_ne (x y : BitVec n) (h1 : x <= y) (h2 : ¬ x = y) : x < y := by
  revert h1 h2
  let ⟨x, lt⟩ := x
  let ⟨y, lt⟩ := y
  simp
  exact Nat.lt_of_le_of_ne

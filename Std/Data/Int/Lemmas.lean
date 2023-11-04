/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Deniz Aydin, Floris van Doorn, Mario Carneiro
-/
import Std.Classes.Cast
import Std.Data.Nat.Lemmas
import Std.Data.Int.Basic
import Std.Data.Option.Basic
import Std.Tactic.NormCast.Lemmas
import Std.Tactic.RCases

open Nat

namespace Int

@[simp] theorem ofNat_eq_coe : ofNat n = Nat.cast n := rfl

@[simp] theorem ofNat_zero : ((0 : Nat) : Int) = 0 := rfl

@[simp] theorem ofNat_one  : ((1 : Nat) : Int) = 1 := rfl

@[simp] theorem default_eq_zero : default = (0 : Int) := rfl

/- ## Definitions of basic functions -/

theorem subNatNat_of_sub_eq_zero {m n : Nat} (h : n - m = 0) : subNatNat m n = ↑(m - n) := by
  rw [subNatNat, h, ofNat_eq_coe]

theorem subNatNat_of_sub_eq_succ {m n k : Nat} (h : n - m = succ k) : subNatNat m n = -[k+1] := by
  rw [subNatNat, h]

@[local simp] protected theorem neg_zero : -(0:Int) = 0 := rfl

theorem ofNat_add (n m : Nat) : (↑(n + m) : Int) = n + m := rfl
theorem ofNat_mul (n m : Nat) : (↑(n * m) : Int) = n * m := rfl
theorem ofNat_succ (n : Nat) : (succ n : Int) = n + 1 := rfl

@[local simp] theorem neg_ofNat_zero : -((0 : Nat) : Int) = 0 := rfl
@[local simp] theorem neg_ofNat_succ (n : Nat) : -(succ n : Int) = -[n+1] := rfl
@[local simp] theorem neg_negSucc (n : Nat) : -(-[n+1]) = succ n := rfl

theorem negSucc_coe (n : Nat) : -[n+1] = -↑(n + 1) := rfl

theorem negOfNat_eq : negOfNat n = -ofNat n := rfl

/- ## These are only for internal use -/

@[simp] theorem add_def {a b : Int} : Int.add a b = a + b := rfl

@[local simp] theorem ofNat_add_ofNat (m n : Nat) : (↑m + ↑n : Int) = ↑(m + n) := rfl
@[local simp] theorem ofNat_add_negSucc (m n : Nat) : ↑m + -[n+1] = subNatNat m (succ n) := rfl
@[local simp] theorem negSucc_add_ofNat (m n : Nat) : -[m+1] + ↑n = subNatNat n (succ m) := rfl
@[local simp] theorem negSucc_add_negSucc (m n : Nat) : -[m+1] + -[n+1] = -[succ (m + n) +1] := rfl

@[simp] theorem mul_def {a b : Int} : Int.mul a b = a * b := rfl

@[local simp] theorem ofNat_mul_ofNat (m n : Nat) : (↑m * ↑n : Int) = ↑(m * n) := rfl
@[local simp] theorem ofNat_mul_negSucc' (m n : Nat) : ↑m * -[n+1] = negOfNat (m * succ n) := rfl
@[local simp] theorem negSucc_mul_ofNat' (m n : Nat) : -[m+1] * ↑n = negOfNat (succ m * n) := rfl
@[local simp] theorem negSucc_mul_negSucc' (m n : Nat) :
    -[m+1] * -[n+1] = ofNat (succ m * succ n) := rfl

/- ## some basic functions and properties -/

theorem ofNat_inj : ((m : Nat) : Int) = (n : Nat) ↔ m = n := ⟨ofNat.inj, congrArg _⟩

theorem ofNat_eq_zero : ((n : Nat) : Int) = 0 ↔ n = 0 := ofNat_inj

theorem ofNat_ne_zero : ((n : Nat) : Int) ≠ 0 ↔ n ≠ 0 := not_congr ofNat_eq_zero

theorem negSucc_inj : negSucc m = negSucc n ↔ m = n := ⟨negSucc.inj, fun H => by simp [H]⟩

theorem negSucc_eq (n : Nat) : -[n+1] = -((n : Int) + 1) := rfl

@[simp] theorem negSucc_ne_zero (n : Nat) : -[n+1] ≠ 0 := fun.

@[simp] theorem zero_ne_negSucc (n : Nat) : 0 ≠ -[n+1] := fun.

/- ## neg -/

@[simp] protected theorem neg_neg : ∀ a : Int, -(-a) = a
  | 0      => rfl
  | succ _ => rfl
  | -[_+1] => rfl

protected theorem neg_inj {a b : Int} : -a = -b ↔ a = b :=
  ⟨fun h => by rw [← Int.neg_neg a, ← Int.neg_neg b, h], congrArg _⟩

protected theorem neg_eq_zero : -a = 0 ↔ a = 0 := Int.neg_inj (b := 0)

protected theorem neg_ne_zero : -a ≠ 0 ↔ a ≠ 0 := not_congr Int.neg_eq_zero

protected theorem sub_eq_add_neg {a b : Int} : a - b = a + -b := rfl

theorem add_neg_one (i : Int) : i + -1 = i - 1 := rfl

/- ## basic properties of subNatNat -/

-- @[elabAsElim] -- TODO(Mario): unexpected eliminator resulting type
theorem subNatNat_elim (m n : Nat) (motive : Nat → Nat → Int → Prop)
    (hp : ∀ i n, motive (n + i) n i)
    (hn : ∀ i m, motive m (m + i + 1) -[i+1]) :
    motive m n (subNatNat m n) := by
  unfold subNatNat
  match h : n - m with
  | 0 =>
    have ⟨k, h⟩ := Nat.le.dest (Nat.le_of_sub_eq_zero h)
    rw [h.symm, Nat.add_sub_cancel_left]; apply hp
  | succ k =>
    rw [Nat.sub_eq_iff_eq_add (Nat.le_of_lt (Nat.lt_of_sub_eq_succ h))] at h
    rw [h, Nat.add_comm]; apply hn

theorem subNatNat_add_left : subNatNat (m + n) m = n := by
  unfold subNatNat
  rw [Nat.sub_eq_zero_of_le (Nat.le_add_right ..), Nat.add_sub_cancel_left, ofNat_eq_coe]

theorem subNatNat_add_right : subNatNat m (m + n + 1) = negSucc n := by
  simp [subNatNat, Nat.add_assoc, Nat.add_sub_cancel_left]

theorem subNatNat_add_add (m n k : Nat) : subNatNat (m + k) (n + k) = subNatNat m n := by
  apply subNatNat_elim m n (fun m n i => subNatNat (m + k) (n + k) = i)
  · intro i j
    rw [Nat.add_assoc, Nat.add_comm i k, ← Nat.add_assoc]
    exact subNatNat_add_left
  · intro i j
    rw [Nat.add_assoc j i 1, Nat.add_comm j (i+1), Nat.add_assoc, Nat.add_comm (i+1) (j+k)]
    exact subNatNat_add_right

theorem subNatNat_of_le {m n : Nat} (h : n ≤ m) : subNatNat m n = ↑(m - n) :=
  subNatNat_of_sub_eq_zero (Nat.sub_eq_zero_of_le h)

theorem subNatNat_of_lt {m n : Nat} (h : m < n) : subNatNat m n = -[pred (n - m) +1] :=
  subNatNat_of_sub_eq_succ <| (Nat.succ_pred_eq_of_pos (Nat.sub_pos_of_lt h)).symm

/- ## natAbs -/

@[simp] theorem natAbs_ofNat (n : Nat) : natAbs ↑n = n := rfl
@[simp] theorem natAbs_negSucc (n : Nat) : natAbs -[n+1] = n.succ := rfl
@[simp] theorem natAbs_zero : natAbs (0 : Int) = (0 : Nat) := rfl
@[simp] theorem natAbs_one : natAbs (1 : Int) = (1 : Nat) := rfl

@[simp] theorem natAbs_eq_zero : natAbs a = 0 ↔ a = 0 :=
  ⟨fun H => match a with
    | ofNat _ => congrArg ofNat H
    | -[_+1]  => absurd H (succ_ne_zero _),
  fun e => e ▸ rfl⟩

theorem natAbs_ne_zero {a : Int} : a.natAbs ≠ 0 ↔ a ≠ 0 := not_congr Int.natAbs_eq_zero

theorem natAbs_pos : 0 < natAbs a ↔ a ≠ 0 := by rw [Nat.pos_iff_ne_zero, Ne, natAbs_eq_zero]

theorem natAbs_mul_self : ∀ {a : Int}, ↑(natAbs a * natAbs a) = a * a
  | ofNat _ => rfl
  | -[_+1]  => rfl

@[simp] theorem natAbs_neg : ∀ (a : Int), natAbs (-a) = natAbs a
  | 0      => rfl
  | succ _ => rfl
  | -[_+1] => rfl

theorem natAbs_eq : ∀ (a : Int), a = natAbs a ∨ a = -↑(natAbs a)
  | ofNat _ => Or.inl rfl
  | -[_+1]  => Or.inr rfl

theorem eq_nat_or_neg (a : Int) : ∃ n : Nat, a = n ∨ a = -↑n := ⟨_, natAbs_eq a⟩

theorem natAbs_negOfNat (n : Nat) : natAbs (negOfNat n) = n := by
  cases n <;> rfl

theorem natAbs_mul (a b : Int) : natAbs (a * b) = natAbs a * natAbs b := by
  cases a <;> cases b <;>
    simp only [← Int.mul_def, Int.mul, natAbs_negOfNat] <;> simp only [natAbs]

theorem natAbs_mul_natAbs_eq {a b : Int} {c : Nat}
    (h : a * b = (c : Int)) : a.natAbs * b.natAbs = c := by rw [← natAbs_mul, h, natAbs]

@[simp] theorem natAbs_mul_self' (a : Int) : (natAbs a * natAbs a : Int) = a * a := by
  rw [← Int.ofNat_mul, natAbs_mul_self]

theorem natAbs_eq_natAbs_iff {a b : Int} : a.natAbs = b.natAbs ↔ a = b ∨ a = -b := by
  constructor <;> intro h
  · cases Int.natAbs_eq a with
    | inl h₁ | inr h₁ =>
      cases Int.natAbs_eq b with
      | inl h₂ | inr h₂ => rw [h₁, h₂]; simp [h]
  · cases h with (subst a; try rfl)
    | inr h => rw [Int.natAbs_neg]

theorem natAbs_eq_iff {a : Int} {n : Nat} : a.natAbs = n ↔ a = n ∨ a = -↑n := by
  rw [← Int.natAbs_eq_natAbs_iff, Int.natAbs_ofNat]

/- ## sign -/

@[simp] theorem sign_zero : sign 0 = 0 := rfl
@[simp] theorem sign_one : sign 1 = 1 := rfl
theorem sign_neg_one : sign (-1) = -1 := rfl

theorem sign_of_succ (n : Nat) : sign (Nat.succ n) = 1 := rfl

theorem natAbs_sign (z : Int) : z.sign.natAbs = if z = 0 then 0 else 1 :=
  match z with | 0 | succ _ | -[_+1] => rfl

theorem natAbs_sign_of_nonzero {z : Int} (hz : z ≠ 0) : z.sign.natAbs = 1 := by
  rw [Int.natAbs_sign, if_neg hz]

theorem sign_ofNat_of_nonzero {n : Nat} (hn : n ≠ 0) : Int.sign n = 1 :=
  match n, Nat.exists_eq_succ_of_ne_zero hn with
  | _, ⟨n, rfl⟩ => Int.sign_of_succ n

@[simp] theorem sign_neg (z : Int) : Int.sign (-z) = -Int.sign z := by
  match z with | 0 | succ _ | -[_+1] => rfl

/- # ring properties -/

/- addition -/

protected theorem add_comm : ∀ a b : Int, a + b = b + a
  | ofNat n, ofNat m => by simp [Nat.add_comm]
  | ofNat _, -[_+1]  => rfl
  | -[_+1],  ofNat _ => rfl
  | -[_+1],  -[_+1]  => by simp [Nat.add_comm]

@[local simp] protected theorem add_zero : ∀ a : Int, a + 0 = a
  | ofNat _ => rfl
  | -[_+1]  => rfl

@[local simp] protected theorem zero_add (a : Int) : 0 + a = a := Int.add_comm .. ▸ a.add_zero

theorem ofNat_add_negSucc_of_lt (h : m < n.succ) : ofNat m + -[n+1] = -[n - m+1] :=
  show subNatNat .. = _ by simp [succ_sub (le_of_lt_succ h), subNatNat]

theorem subNatNat_sub (h : n ≤ m) (k : Nat) : subNatNat (m - n) k = subNatNat m (k + n) := by
  rwa [← subNatNat_add_add _ _ n, Nat.sub_add_cancel]

theorem subNatNat_add (m n k : Nat) : subNatNat (m + n) k = m + subNatNat n k := by
  cases n.lt_or_ge k with
  | inl h' =>
    simp [subNatNat_of_lt h', succ_pred_eq_of_pos (Nat.sub_pos_of_lt h')]
    conv => lhs; rw [← Nat.sub_add_cancel (Nat.le_of_lt h')]
    apply subNatNat_add_add
  | inr h' => simp [subNatNat_of_le h',
      subNatNat_of_le (Nat.le_trans h' (le_add_left ..)), Nat.add_sub_assoc h']

theorem subNatNat_add_negSucc (m n k : Nat) :
    subNatNat m n + -[k+1] = subNatNat m (n + succ k) := by
  have h := Nat.lt_or_ge m n
  cases h with
  | inr h' =>
    rw [subNatNat_of_le h']
    simp
    rw [subNatNat_sub h', Nat.add_comm]
  | inl h' =>
    have h₂ : m < n + succ k := Nat.lt_of_lt_of_le h' (le_add_right _ _)
    have h₃ : m ≤ n + k := le_of_succ_le_succ h₂
    rw [subNatNat_of_lt h', subNatNat_of_lt h₂]
    simp [Nat.add_comm]
    rw [← add_succ, succ_pred_eq_of_pos (Nat.sub_pos_of_lt h'), add_succ, succ_sub h₃,
      Nat.pred_succ]
    rw [Nat.add_comm n, Nat.add_sub_assoc (Nat.le_of_lt h')]

protected theorem add_assoc : ∀ a b c : Int, a + b + c = a + (b + c)
  | (m:Nat), (n:Nat), c => aux1 ..
  | Nat.cast m, b, Nat.cast k => by
    rw [Int.add_comm, ← aux1, Int.add_comm k, aux1, Int.add_comm b]
  | a, (n:Nat), (k:Nat) => by
    rw [Int.add_comm, Int.add_comm a, ← aux1, Int.add_comm a, Int.add_comm k]
  | -[m+1], -[n+1], (k:Nat) => aux2 ..
  | -[m+1], (n:Nat), -[k+1] => by
    rw [Int.add_comm, ← aux2, Int.add_comm n, ← aux2, Int.add_comm -[m+1]]
  | (m:Nat), -[n+1], -[k+1] => by
    rw [Int.add_comm, Int.add_comm m, Int.add_comm m, ← aux2, Int.add_comm -[k+1]]
  | -[m+1], -[n+1], -[k+1] => by
    simp [add_succ, Nat.add_comm, Nat.add_left_comm, neg_ofNat_succ]
where
  aux1 (m n : Nat) : ∀ c : Int, m + n + c = m + (n + c)
    | (k:Nat) => by simp [Nat.add_assoc]
    | -[k+1]  => by simp [subNatNat_add]
  aux2 (m n k : Nat) : -[m+1] + -[n+1] + k = -[m+1] + (-[n+1] + k) := by
    simp [add_succ]
    rw [Int.add_comm, subNatNat_add_negSucc]
    simp [add_succ, succ_add, Nat.add_comm]

protected theorem add_left_comm (a b c : Int) : a + (b + c) = b + (a + c) := by
  rw [← Int.add_assoc, Int.add_comm a, Int.add_assoc]

protected theorem add_right_comm (a b c : Int) : a + b + c = a + c + b := by
  rw [Int.add_assoc, Int.add_comm b, ← Int.add_assoc]

/- ## negation -/

theorem subNatNat_self : ∀ n, subNatNat n n = 0
  | 0      => rfl
  | succ m => by rw [subNatNat_of_sub_eq_zero (Nat.sub_self ..), Nat.sub_self, ofNat_zero]

attribute [local simp] subNatNat_self

@[local simp] protected theorem add_left_neg : ∀ a : Int, -a + a = 0
  | 0      => rfl
  | succ m => by simp
  | -[m+1] => by simp

@[local simp] protected theorem add_right_neg (a : Int) : a + -a = 0 := by
  rw [Int.add_comm, Int.add_left_neg]

@[simp] protected theorem neg_eq_of_add_eq_zero {a b : Int} (h : a + b = 0) : -a = b := by
  rw [← Int.add_zero (-a), ← h, ← Int.add_assoc, Int.add_left_neg, Int.zero_add]

protected theorem eq_neg_of_eq_neg {a b : Int} (h : a = -b) : b = -a := by
  rw [h, Int.neg_neg]

protected theorem eq_neg_comm {a b : Int} : a = -b ↔ b = -a :=
  ⟨Int.eq_neg_of_eq_neg, Int.eq_neg_of_eq_neg⟩

protected theorem neg_eq_comm {a b : Int} : -a = b ↔ -b = a := by
  rw [eq_comm, Int.eq_neg_comm, eq_comm]

protected theorem neg_add_cancel_left (a b : Int) : -a + (a + b) = b := by
  rw [← Int.add_assoc, Int.add_left_neg, Int.zero_add]

protected theorem add_neg_cancel_left (a b : Int) : a + (-a + b) = b := by
  rw [← Int.add_assoc, Int.add_right_neg, Int.zero_add]

protected theorem add_neg_cancel_right (a b : Int) : a + b + -b = a := by
  rw [Int.add_assoc, Int.add_right_neg, Int.add_zero]

protected theorem neg_add_cancel_right (a b : Int) : a + -b + b = a := by
  rw [Int.add_assoc, Int.add_left_neg, Int.add_zero]

protected theorem add_left_cancel {a b c : Int} (h : a + b = a + c) : b = c := by
  have h₁ : -a + (a + b) = -a + (a + c) := by rw [h]
  simp [← Int.add_assoc, Int.add_left_neg, Int.zero_add] at h₁; exact h₁

@[local simp] protected theorem neg_add {a b : Int} : -(a + b) = -a + -b := by
  apply Int.add_left_cancel (a := a + b)
  rw [Int.add_right_neg, Int.add_comm a, ← Int.add_assoc, Int.add_assoc b,
    Int.add_right_neg, Int.add_zero, Int.add_right_neg]

/- ## subtraction -/

@[simp] theorem negSucc_sub_one (n : Nat) : -[n+1] - 1 = -[n + 1 +1] := rfl

protected theorem sub_self (a : Int) : a - a = 0 := by
  rw [Int.sub_eq_add_neg, Int.add_right_neg]

protected theorem sub_zero (a : Int) : a - 0 = a := by simp [Int.sub_eq_add_neg]

protected theorem zero_sub (a : Int) : 0 - a = -a := by simp [Int.sub_eq_add_neg]

protected theorem sub_eq_zero_of_eq {a b : Int} (h : a = b) : a - b = 0 := by
  rw [h, Int.sub_self]

protected theorem eq_of_sub_eq_zero {a b : Int} (h : a - b = 0) : a = b := by
  have : 0 + b = b := by rw [Int.zero_add]
  have : a - b + b = b := by rwa [h]
  rwa [Int.sub_eq_add_neg, Int.neg_add_cancel_right] at this

protected theorem sub_eq_zero {a b : Int} : a - b = 0 ↔ a = b :=
  ⟨Int.eq_of_sub_eq_zero, Int.sub_eq_zero_of_eq⟩

protected theorem sub_sub (a b c : Int) : a - b - c = a - (b + c) := by
  simp [Int.sub_eq_add_neg, Int.add_assoc]

protected theorem neg_sub (a b : Int) : -(a - b) = b - a := by
  simp [Int.sub_eq_add_neg, Int.add_comm]

protected theorem sub_sub_self (a b : Int) : a - (a - b) = b := by
  simp [Int.sub_eq_add_neg, ← Int.add_assoc]

protected theorem sub_neg (a b : Int) : a - -b = a + b := by simp [Int.sub_eq_add_neg]

/- ## multiplication -/

@[simp] theorem ofNat_mul_negSucc (m n : Nat) : (m : Int) * -[n+1] = -↑(m * succ n) := rfl

@[simp] theorem negSucc_mul_ofNat (m n : Nat) : -[m+1] * n = -↑(succ m * n) := rfl

@[simp] theorem negSucc_mul_negSucc (m n : Nat) : -[m+1] * -[n+1] = succ m * succ n := rfl

protected theorem mul_comm (a b : Int) : a * b = b * a := by
  cases a <;> cases b <;> simp [Nat.mul_comm]

theorem ofNat_mul_negOfNat (m n : Nat) : (m : Nat) * negOfNat n = negOfNat (m * n) := by
  cases n <;> rfl

theorem negOfNat_mul_ofNat (m n : Nat) : negOfNat m * (n : Nat) = negOfNat (m * n) := by
  rw [Int.mul_comm]; simp [ofNat_mul_negOfNat, Nat.mul_comm]

theorem negSucc_mul_negOfNat (m n : Nat) : -[m+1] * negOfNat n = ofNat (succ m * n) := by
  cases n <;> rfl

theorem negOfNat_mul_negSucc (m n : Nat) : negOfNat n * -[m+1] = ofNat (n * succ m) := by
  rw [Int.mul_comm, negSucc_mul_negOfNat, Nat.mul_comm]

attribute [local simp] ofNat_mul_negOfNat negOfNat_mul_ofNat
  negSucc_mul_negOfNat negOfNat_mul_negSucc

protected theorem mul_assoc (a b c : Int) : a * b * c = a * (b * c) := by
  cases a <;> cases b <;> cases c <;> simp [Nat.mul_assoc]

protected theorem mul_left_comm (a b c : Int) : a * (b * c) = b * (a * c) := by
  rw [← Int.mul_assoc, ← Int.mul_assoc, Int.mul_comm a]

protected theorem mul_right_comm (a b c : Int) : a * b * c = a * c * b := by
  rw [Int.mul_assoc, Int.mul_assoc, Int.mul_comm b]

@[simp] protected theorem mul_zero (a : Int) : a * 0 = 0 := by cases a <;> rfl

@[simp] protected theorem zero_mul (a : Int) : 0 * a = 0 := Int.mul_comm .. ▸ a.mul_zero

theorem negOfNat_eq_subNatNat_zero (n) : negOfNat n = subNatNat 0 n := by cases n <;> rfl

theorem ofNat_mul_subNatNat (m n k : Nat) :
    m * subNatNat n k = subNatNat (m * n) (m * k) := by
  cases m with
  | zero => simp [ofNat_zero, Int.zero_mul, Nat.zero_mul]
  | succ m => cases n.lt_or_ge k with
    | inl h =>
      have h' : succ m * n < succ m * k := Nat.mul_lt_mul_of_pos_left h (Nat.succ_pos m)
      simp [subNatNat_of_lt h, subNatNat_of_lt h']
      rw [succ_pred_eq_of_pos (Nat.sub_pos_of_lt h), ← neg_ofNat_succ, Nat.mul_sub_left_distrib,
        ← succ_pred_eq_of_pos (Nat.sub_pos_of_lt h')]; rfl
    | inr h =>
      have h' : succ m * k ≤ succ m * n := Nat.mul_le_mul_left _ h
      simp [subNatNat_of_le h, subNatNat_of_le h', Nat.mul_sub_left_distrib]

theorem negOfNat_add (m n : Nat) : negOfNat m + negOfNat n = negOfNat (m + n) := by
  cases m <;> cases n <;> simp [Nat.succ_add] <;> rfl

theorem negSucc_mul_subNatNat (m n k : Nat) :
    -[m+1] * subNatNat n k = subNatNat (succ m * k) (succ m * n) := by
  cases n.lt_or_ge k with
  | inl h =>
    have h' : succ m * n < succ m * k := Nat.mul_lt_mul_of_pos_left h (Nat.succ_pos m)
    rw [subNatNat_of_lt h, subNatNat_of_le (Nat.le_of_lt h')]
    simp [succ_pred_eq_of_pos (Nat.sub_pos_of_lt h), Nat.mul_sub_left_distrib]
  | inr h => cases Nat.lt_or_ge k n with
    | inl h' =>
      have h₁ : succ m * n > succ m * k := Nat.mul_lt_mul_of_pos_left h' (Nat.succ_pos m)
      rw [subNatNat_of_le h, subNatNat_of_lt h₁, negSucc_mul_ofNat,
        Nat.mul_sub_left_distrib, ← succ_pred_eq_of_pos (Nat.sub_pos_of_lt h₁)]; rfl
    | inr h' => rw [Nat.le_antisymm h h', subNatNat_self, subNatNat_self, Int.mul_zero]

attribute [local simp] ofNat_mul_subNatNat negOfNat_add negSucc_mul_subNatNat

protected theorem mul_add : ∀ a b c : Int, a * (b + c) = a * b + a * c
  | (m:Nat), (n:Nat), (k:Nat) => by simp [Nat.left_distrib]
  | (m:Nat), (n:Nat), -[k+1]  => by
    simp [negOfNat_eq_subNatNat_zero]; rw [← subNatNat_add]; rfl
  | (m:Nat), -[n+1],  (k:Nat) => by
    simp [negOfNat_eq_subNatNat_zero]; rw [Int.add_comm, ← subNatNat_add]; rfl
  | (m:Nat), -[n+1],  -[k+1]  => by simp; rw [← Nat.left_distrib, succ_add]; rfl
  | -[m+1],  (n:Nat), (k:Nat) => by simp [Nat.mul_comm]; rw [← Nat.right_distrib, Nat.mul_comm]
  | -[m+1],  (n:Nat), -[k+1]  => by
    simp [negOfNat_eq_subNatNat_zero]; rw [Int.add_comm, ← subNatNat_add]; rfl
  | -[m+1],  -[n+1],  (k:Nat) => by simp [negOfNat_eq_subNatNat_zero]; rw [← subNatNat_add]; rfl
  | -[m+1],  -[n+1],  -[k+1]  => by simp; rw [← Nat.left_distrib, succ_add]; rfl

protected theorem add_mul (a b c : Int) : (a + b) * c = a * c + b * c := by
  simp [Int.mul_comm, Int.mul_add]

protected theorem neg_mul_eq_neg_mul (a b : Int) : -(a * b) = -a * b :=
  Int.neg_eq_of_add_eq_zero <| by rw [← Int.add_mul, Int.add_right_neg, Int.zero_mul]

protected theorem neg_mul_eq_mul_neg (a b : Int) : -(a * b) = a * -b :=
  Int.neg_eq_of_add_eq_zero <| by rw [← Int.mul_add, Int.add_right_neg, Int.mul_zero]

@[local simp] protected theorem neg_mul (a b : Int) : -a * b = -(a * b) :=
  (Int.neg_mul_eq_neg_mul a b).symm

@[local simp] protected theorem mul_neg (a b : Int) : a * -b = -(a * b) :=
  (Int.neg_mul_eq_mul_neg a b).symm

protected theorem neg_mul_neg (a b : Int) : -a * -b = a * b := by simp

protected theorem neg_mul_comm (a b : Int) : -a * b = a * -b := by simp

protected theorem mul_sub (a b c : Int) : a * (b - c) = a * b - a * c := by
  simp [Int.sub_eq_add_neg, Int.mul_add]

protected theorem sub_mul (a b c : Int) : (a - b) * c = a * c - b * c := by
  simp [Int.sub_eq_add_neg, Int.add_mul]

protected theorem zero_ne_one : (0 : Int) ≠ 1 := fun.

@[simp] protected theorem sub_add_cancel (a b : Int) : a - b + b = a :=
  Int.neg_add_cancel_right a b

@[simp] protected theorem add_sub_cancel (a b : Int) : a + b - b = a :=
  Int.add_neg_cancel_right a b

protected theorem add_sub_assoc (a b c : Int) : a + b - c = a + (b - c) := by
  rw [Int.sub_eq_add_neg, Int.add_assoc, ← Int.sub_eq_add_neg]

theorem ofNat_sub (h : m ≤ n) : ((n - m : Nat) : Int) = n - m := by
  match m with
  | 0 => rfl
  | succ m =>
    show ofNat (n - succ m) = subNatNat n (succ m)
    rw [subNatNat, Nat.sub_eq_zero_of_le h]

theorem negSucc_coe' (n : Nat) : -[n+1] = -↑n - 1 := by
  rw [Int.sub_eq_add_neg, ← Int.neg_add]; rfl

protected theorem subNatNat_eq_coe {m n : Nat} : subNatNat m n = ↑m - ↑n := by
  apply subNatNat_elim m n fun m n i => i = m - n
  · intros i n
    rw [Int.ofNat_add, Int.sub_eq_add_neg, Int.add_assoc, Int.add_left_comm,
      Int.add_right_neg, Int.add_zero]
  · intros i n
    simp only [negSucc_coe, ofNat_add, Int.sub_eq_add_neg, Int.neg_add, ← Int.add_assoc]
    rw [← @Int.sub_eq_add_neg n, ← ofNat_sub, Nat.sub_self, ofNat_zero, Int.zero_add]
    apply Nat.le_refl

theorem toNat_sub (m n : Nat) : toNat (m - n) = m - n := by
  rw [← Int.subNatNat_eq_coe]
  refine subNatNat_elim m n (fun m n i => toNat i = m - n) (fun i n => ?_) (fun i n => ?_)
  · exact (Nat.add_sub_cancel_left ..).symm
  · dsimp; rw [Nat.add_assoc, Nat.sub_eq_zero_of_le (Nat.le_add_right ..)]; rfl

@[simp] protected theorem one_mul : ∀ a : Int, 1 * a = a
  | ofNat n => show ofNat (1 * n) = ofNat n by rw [Nat.one_mul]
  | -[n+1]  => show -[1 * n +1] = -[n+1] by rw [Nat.one_mul]

@[simp] protected theorem mul_one (a : Int) : a * 1 = a := by rw [Int.mul_comm, Int.one_mul]

protected theorem mul_neg_one (a : Int) : a * -1 = -a := by rw [Int.mul_neg, Int.mul_one]

protected theorem neg_eq_neg_one_mul : ∀ a : Int, -a = -1 * a
  | 0      => rfl
  | succ n => show _ = -[1 * n +1] by rw [Nat.one_mul]; rfl
  | -[n+1] => show _ = ofNat _ by rw [Nat.one_mul]; rfl

theorem sign_mul_natAbs : ∀ a : Int, sign a * natAbs a = a
  | 0      => rfl
  | succ _ => Int.one_mul _
  | -[_+1] => (Int.neg_eq_neg_one_mul _).symm

@[simp] theorem sign_mul : ∀ a b, sign (a * b) = sign a * sign b
  | a, 0 | 0, b => by simp [Int.mul_zero, Int.zero_mul]
  | succ _, succ _ | succ _, -[_+1] | -[_+1], succ _ | -[_+1], -[_+1] => rfl

/-! ## Order properties of the integers -/

theorem nonneg_def {a : Int} : NonNeg a ↔ ∃ n : Nat, a = n :=
  ⟨fun ⟨n⟩ => ⟨n, rfl⟩, fun h => match a, h with | _, ⟨n, rfl⟩ => ⟨n⟩⟩

theorem NonNeg.elim {a : Int} : NonNeg a → ∃ n : Nat, a = n := nonneg_def.1

theorem nonneg_or_nonneg_neg : ∀ (a : Int), NonNeg a ∨ NonNeg (-a)
  | (_:Nat) => .inl ⟨_⟩
  | -[_+1]  => .inr ⟨_⟩

theorem le_def (a b : Int) : a ≤ b ↔ NonNeg (b - a) := .rfl

theorem lt_iff_add_one_le (a b : Int) : a < b ↔ a + 1 ≤ b := .rfl

theorem le.intro_sub {a b : Int} (n : Nat) (h : b - a = n) : a ≤ b := by
  simp [le_def, h]; constructor

theorem le.intro {a b : Int} (n : Nat) (h : a + n = b) : a ≤ b :=
  le.intro_sub n <| by rw [← h, Int.add_comm]; simp [Int.sub_eq_add_neg, Int.add_assoc]

theorem le.dest_sub {a b : Int} (h : a ≤ b) : ∃ n : Nat, b - a = n := nonneg_def.1 h

theorem le.dest {a b : Int} (h : a ≤ b) : ∃ n : Nat, a + n = b :=
  let ⟨n, h₁⟩ := le.dest_sub h
  ⟨n, by rw [← h₁, Int.add_comm]; simp [Int.sub_eq_add_neg, Int.add_assoc]⟩

protected theorem le_total (a b : Int) : a ≤ b ∨ b ≤ a :=
  (nonneg_or_nonneg_neg (b - a)).imp_right fun H => by
    rwa [show -(b - a) = a - b by simp [Int.add_comm, Int.sub_eq_add_neg]] at H

@[simp, norm_cast] theorem ofNat_le {m n : Nat} : (↑m : Int) ≤ ↑n ↔ m ≤ n :=
  ⟨fun h =>
    let ⟨k, hk⟩ := le.dest h
    Nat.le.intro <| Int.ofNat.inj <| (Int.ofNat_add m k).trans hk,
  fun h =>
    let ⟨k, (hk : m + k = n)⟩ := Nat.le.dest h
    le.intro k (by rw [← hk]; rfl)⟩

theorem ofNat_zero_le (n : Nat) : 0 ≤ (↑n : Int) := ofNat_le.2 n.zero_le

theorem eq_ofNat_of_zero_le {a : Int} (h : 0 ≤ a) : ∃ n : Nat, a = n := by
  have t := le.dest_sub h; rwa [Int.sub_zero] at t

theorem eq_succ_of_zero_lt {a : Int} (h : 0 < a) : ∃ n : Nat, a = n.succ :=
  let ⟨n, (h : ↑(1 + n) = a)⟩ := le.dest h
  ⟨n, by rw [Nat.add_comm] at h; exact h.symm⟩

theorem lt_add_succ (a : Int) (n : Nat) : a < a + Nat.succ n :=
  le.intro n <| by rw [Int.add_comm, Int.add_left_comm]; rfl

theorem lt.intro {a b : Int} {n : Nat} (h : a + Nat.succ n = b) : a < b :=
  h ▸ lt_add_succ a n

theorem lt.dest {a b : Int} (h : a < b) : ∃ n : Nat, a + Nat.succ n = b :=
  let ⟨n, h⟩ := le.dest h; ⟨n, by rwa [Int.add_comm, Int.add_left_comm] at h⟩

@[simp, norm_cast] theorem ofNat_lt {n m : Nat} : (↑n : Int) < ↑m ↔ n < m := by
  rw [lt_iff_add_one_le, ← ofNat_succ, ofNat_le]; rfl

@[simp, norm_cast] theorem ofNat_pos {n : Nat} : 0 < (↑n : Int) ↔ 0 < n := ofNat_lt

theorem ofNat_nonneg (n : Nat) : 0 ≤ (n : Int) := ⟨_⟩

theorem ofNat_succ_pos (n : Nat) : 0 < (succ n : Int) := ofNat_lt.2 <| Nat.succ_pos _

@[simp] protected theorem le_refl (a : Int) : a ≤ a :=
  le.intro _ (Int.add_zero a)

protected theorem le_trans {a b c : Int} (h₁ : a ≤ b) (h₂ : b ≤ c) : a ≤ c :=
  let ⟨n, hn⟩ := le.dest h₁; let ⟨m, hm⟩ := le.dest h₂
  le.intro (n + m) <| by rw [← hm, ← hn, Int.add_assoc, ofNat_add]

protected theorem le_antisymm {a b : Int} (h₁ : a ≤ b) (h₂ : b ≤ a) : a = b := by
  let ⟨n, hn⟩ := le.dest h₁; let ⟨m, hm⟩ := le.dest h₂
  have := hn; rw [← hm, Int.add_assoc, ← ofNat_add] at this
  have := Int.ofNat.inj <| Int.add_left_cancel <| this.trans (Int.add_zero _).symm
  rw [← hn, Nat.eq_zero_of_add_eq_zero_left this, ofNat_zero, Int.add_zero a]

protected theorem lt_irrefl (a : Int) : ¬a < a := fun H =>
  let ⟨n, hn⟩ := lt.dest H
  have : (a+Nat.succ n) = a+0 := by
    rw [hn, Int.add_zero]
  have : Nat.succ n = 0 := Int.ofNat.inj (Int.add_left_cancel this)
  show False from Nat.succ_ne_zero _ this

protected theorem ne_of_lt {a b : Int} (h : a < b) : a ≠ b := fun e => by
  cases e; exact Int.lt_irrefl _ h

protected theorem ne_of_gt {a b : Int} (h : b < a) : a ≠ b := (Int.ne_of_lt h).symm

protected theorem le_of_lt {a b : Int} (h : a < b) : a ≤ b :=
  let ⟨_, hn⟩ := lt.dest h; le.intro _ hn

protected theorem lt_iff_le_and_ne {a b : Int} : a < b ↔ a ≤ b ∧ a ≠ b := by
  refine ⟨fun h => ⟨Int.le_of_lt h, Int.ne_of_lt h⟩, fun ⟨aleb, aneb⟩ => ?_⟩
  let ⟨n, hn⟩ := le.dest aleb
  have : n ≠ 0 := aneb.imp fun eq => by rw [← hn, eq, ofNat_zero, Int.add_zero]
  apply lt.intro; rwa [← Nat.succ_pred_eq_of_pos (Nat.pos_of_ne_zero this)] at hn

theorem lt_succ (a : Int) : a < a + 1 := Int.le_refl _

protected theorem mul_nonneg {a b : Int} (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a * b := by
  let ⟨n, hn⟩ := eq_ofNat_of_zero_le ha
  let ⟨m, hm⟩ := eq_ofNat_of_zero_le hb
  rw [hn, hm, ← ofNat_mul]; apply ofNat_nonneg

protected theorem mul_pos {a b : Int} (ha : 0 < a) (hb : 0 < b) : 0 < a * b := by
  let ⟨n, hn⟩ := eq_succ_of_zero_lt ha
  let ⟨m, hm⟩ := eq_succ_of_zero_lt hb
  rw [hn, hm, ← ofNat_mul]; apply ofNat_succ_pos

protected theorem zero_lt_one : (0 : Int) < 1 := ⟨_⟩

protected theorem lt_iff_le_not_le {a b : Int} : a < b ↔ a ≤ b ∧ ¬b ≤ a := by
  rw [Int.lt_iff_le_and_ne]
  constructor <;> refine fun ⟨h, h'⟩ => ⟨h, h'.imp fun h' => ?_⟩
  · exact Int.le_antisymm h h'
  · subst h'; apply Int.le_refl

protected theorem not_le {a b : Int} : ¬a ≤ b ↔ b < a :=
  ⟨fun h => Int.lt_iff_le_not_le.2 ⟨(Int.le_total ..).resolve_right h, h⟩,
   fun h => (Int.lt_iff_le_not_le.1 h).2⟩

protected theorem not_lt {a b : Int} : ¬a < b ↔ b ≤ a :=
  by rw [← Int.not_le, Decidable.not_not]

protected theorem lt_trichotomy (a b : Int) : a < b ∨ a = b ∨ b < a :=
  if eq : a = b then .inr <| .inl eq else
  if le : a ≤ b then .inl <| Int.lt_iff_le_and_ne.2 ⟨le, eq⟩ else
  .inr <| .inr <| Int.not_le.1 le

protected theorem lt_of_le_of_lt {a b c : Int} (h₁ : a ≤ b) (h₂ : b < c) : a < c :=
  Int.not_le.1 fun h => Int.not_le.2 h₂ (Int.le_trans h h₁)

protected theorem lt_of_lt_of_le {a b c : Int} (h₁ : a < b) (h₂ : b ≤ c) : a < c :=
  Int.not_le.1 fun h => Int.not_le.2 h₁ (Int.le_trans h₂ h)

protected theorem lt_trans {a b c : Int} (h₁ : a < b) (h₂ : b < c) : a < c :=
  Int.lt_of_le_of_lt (Int.le_of_lt h₁) h₂

protected theorem le_of_not_le {a b : Int} : ¬ a ≤ b → b ≤ a := (Int.le_total a b).resolve_left

protected theorem min_def (n m : Int) : min n m = if n ≤ m then n else m := rfl

protected theorem max_def (n m : Int) : max n m = if n ≤ m then m else n := rfl

protected theorem min_comm (a b : Int) : min a b = min b a := by
  simp [Int.min_def]
  by_cases h₁ : a ≤ b <;> by_cases h₂ : b ≤ a <;> simp [h₁, h₂]
  · exact Int.le_antisymm h₁ h₂
  · cases not_or_intro h₁ h₂ <| Int.le_total ..

protected theorem min_le_right (a b : Int) : min a b ≤ b := by rw [Int.min_def]; split <;> simp [*]

protected theorem min_le_left (a b : Int) : min a b ≤ a := Int.min_comm .. ▸ Int.min_le_right ..

protected theorem le_min {a b c : Int} : a ≤ min b c ↔ a ≤ b ∧ a ≤ c :=
  ⟨fun h => ⟨Int.le_trans h (Int.min_le_left ..), Int.le_trans h (Int.min_le_right ..)⟩,
   fun ⟨h₁, h₂⟩ => by rw [Int.min_def]; split <;> assumption⟩

protected theorem min_eq_left {a b : Int} (h : a ≤ b) : min a b = a := by simp [Int.min_def, h]

protected theorem min_eq_right {a b : Int} (h : b ≤ a) : min a b = b := by
  rw [Int.min_comm a b]; exact Int.min_eq_left h

protected theorem max_comm (a b : Int) : max a b = max b a := by
  simp only [Int.max_def]
  by_cases h₁ : a ≤ b <;> by_cases h₂ : b ≤ a <;> simp [h₁, h₂]
  · exact Int.le_antisymm h₂ h₁
  · cases not_or_intro h₁ h₂ <| Int.le_total ..

protected theorem le_max_left (a b : Int) : a ≤ max a b := by rw [Int.max_def]; split <;> simp [*]

protected theorem le_max_right (a b : Int) : b ≤ max a b := Int.max_comm .. ▸ Int.le_max_left ..

protected theorem max_le {a b c : Int} : max a b ≤ c ↔ a ≤ c ∧ b ≤ c :=
  ⟨fun h => ⟨Int.le_trans (Int.le_max_left ..) h, Int.le_trans (Int.le_max_right ..) h⟩,
   fun ⟨h₁, h₂⟩ => by rw [Int.max_def]; split <;> assumption⟩

protected theorem max_eq_right {a b : Int} (h : a ≤ b) : max a b = b := by
  simp [Int.max_def, h, Int.not_lt.2 h]

protected theorem max_eq_left {a b : Int} (h : b ≤ a) : max a b = a := by
  rw [← Int.max_comm b a]; exact Int.max_eq_right h

theorem eq_natAbs_of_zero_le {a : Int} (h : 0 ≤ a) : a = natAbs a := by
  let ⟨n, e⟩ := eq_ofNat_of_zero_le h
  rw [e]; rfl

theorem le_natAbs {a : Int} : a ≤ natAbs a :=
  match Int.le_total 0 a with
  | .inl h => by rw [eq_natAbs_of_zero_le h]; apply Int.le_refl
  | .inr h => Int.le_trans h (ofNat_zero_le _)

theorem negSucc_lt_zero (n : Nat) : -[n+1] < 0 :=
  Int.not_le.1 fun h => let ⟨_, h⟩ := eq_ofNat_of_zero_le h; nomatch h

@[simp] theorem negSucc_not_nonneg (n : Nat) : 0 ≤ -[n+1] ↔ False := by
  simp only [Int.not_le, iff_false]; exact Int.negSucc_lt_zero n

@[simp] theorem negSucc_not_pos (n : Nat) : 0 < -[n+1] ↔ False := by
  simp only [Int.not_lt, iff_false]; constructor

theorem eq_negSucc_of_lt_zero : ∀ {a : Int}, a < 0 → ∃ n : Nat, a = -[n+1]
  | ofNat _, h => absurd h (Int.not_lt.2 (ofNat_zero_le _))
  | -[n+1],  _ => ⟨n, rfl⟩

protected theorem add_le_add_left {a b : Int} (h : a ≤ b) (c : Int) : c + a ≤ c + b :=
  let ⟨n, hn⟩ := le.dest h; le.intro n <| by rw [Int.add_assoc, hn]

protected theorem add_lt_add_left {a b : Int} (h : a < b) (c : Int) : c + a < c + b :=
  Int.lt_iff_le_and_ne.2 ⟨Int.add_le_add_left (Int.le_of_lt h) _, fun heq =>
    b.lt_irrefl <| by rwa [Int.add_left_cancel heq] at h⟩

protected theorem add_le_add_right {a b : Int} (h : a ≤ b) (c : Int) : a + c ≤ b + c :=
  Int.add_comm c a ▸ Int.add_comm c b ▸ Int.add_le_add_left h c

protected theorem add_lt_add_right {a b : Int} (h : a < b) (c : Int) : a + c < b + c :=
  Int.add_comm c a ▸ Int.add_comm c b ▸ Int.add_lt_add_left h c

protected theorem le_of_add_le_add_left {a b c : Int} (h : a + b ≤ a + c) : b ≤ c := by
  have : -a + (a + b) ≤ -a + (a + c) := Int.add_le_add_left h _
  simp [Int.neg_add_cancel_left] at this
  assumption

protected theorem lt_of_add_lt_add_left {a b c : Int} (h : a + b < a + c) : b < c := by
  have : -a + (a + b) < -a + (a + c) := Int.add_lt_add_left h _
  simp [Int.neg_add_cancel_left] at this
  assumption

protected theorem le_of_add_le_add_right {a b c : Int} (h : a + b ≤ c + b) : a ≤ c :=
  Int.le_of_add_le_add_left (a := b) <| by rwa [Int.add_comm b a, Int.add_comm b c]

protected theorem lt_of_add_lt_add_right {a b c : Int} (h : a + b < c + b) : a < c :=
  Int.lt_of_add_lt_add_left (a := b) <| by rwa [Int.add_comm b a, Int.add_comm b c]

protected theorem add_le_add_iff_left (a : Int) : a + b ≤ a + c ↔ b ≤ c :=
  ⟨Int.le_of_add_le_add_left, (Int.add_le_add_left · _)⟩

protected theorem add_lt_add_iff_left (a : Int) : a + b < a + c ↔ b < c :=
  ⟨Int.lt_of_add_lt_add_left, (Int.add_lt_add_left · _)⟩

protected theorem add_le_add_iff_right (c : Int) : a + c ≤ b + c ↔ a ≤ b :=
  ⟨Int.le_of_add_le_add_right, (Int.add_le_add_right · _)⟩

protected theorem add_lt_add_iff_right (c : Int) : a + c < b + c ↔ a < b :=
  ⟨Int.lt_of_add_lt_add_right, (Int.add_lt_add_right · _)⟩

protected theorem add_le_add {a b c d : Int} (h₁ : a ≤ b) (h₂ : c ≤ d) : a + c ≤ b + d :=
  Int.le_trans (Int.add_le_add_right h₁ c) (Int.add_le_add_left h₂ b)

protected theorem le_add_of_nonneg_right {a b : Int} (h : 0 ≤ b) : a ≤ a + b := by
  have : a + b ≥ a + 0 := Int.add_le_add_left h a
  rwa [Int.add_zero] at this

protected theorem le_add_of_nonneg_left {a b : Int} (h : 0 ≤ b) : a ≤ b + a := by
  have : 0 + a ≤ b + a := Int.add_le_add_right h a
  rwa [Int.zero_add] at this

protected theorem add_lt_add {a b c d : Int} (h₁ : a < b) (h₂ : c < d) : a + c < b + d :=
  Int.lt_trans (Int.add_lt_add_right h₁ c) (Int.add_lt_add_left h₂ b)

protected theorem add_lt_add_of_le_of_lt {a b c d : Int} (h₁ : a ≤ b) (h₂ : c < d) :
    a + c < b + d :=
  Int.lt_of_le_of_lt (Int.add_le_add_right h₁ c) (Int.add_lt_add_left h₂ b)

protected theorem add_lt_add_of_lt_of_le {a b c d : Int} (h₁ : a < b) (h₂ : c ≤ d) :
    a + c < b + d :=
  Int.lt_of_lt_of_le (Int.add_lt_add_right h₁ c) (Int.add_le_add_left h₂ b)

protected theorem lt_add_of_pos_right (a : Int) {b : Int} (h : 0 < b) : a < a + b := by
  have : a + 0 < a + b := Int.add_lt_add_left h a
  rwa [Int.add_zero] at this

protected theorem lt_add_of_pos_left (a : Int) {b : Int} (h : 0 < b) : a < b + a := by
  have : 0 + a < b + a := Int.add_lt_add_right h a
  rwa [Int.zero_add] at this

protected theorem add_nonneg {a b : Int} (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a + b :=
  Int.zero_add 0 ▸ Int.add_le_add ha hb

protected theorem add_pos {a b : Int} (ha : 0 < a) (hb : 0 < b) : 0 < a + b :=
  Int.zero_add 0 ▸ Int.add_lt_add ha hb

protected theorem add_pos_of_pos_of_nonneg {a b : Int} (ha : 0 < a) (hb : 0 ≤ b) : 0 < a + b :=
  Int.zero_add 0 ▸ Int.add_lt_add_of_lt_of_le ha hb

protected theorem add_pos_of_nonneg_of_pos {a b : Int} (ha : 0 ≤ a) (hb : 0 < b) : 0 < a + b :=
  Int.zero_add 0 ▸ Int.add_lt_add_of_le_of_lt ha hb

protected theorem add_nonpos {a b : Int} (ha : a ≤ 0) (hb : b ≤ 0) : a + b ≤ 0 :=
  Int.zero_add 0 ▸ Int.add_le_add ha hb

protected theorem add_neg {a b : Int} (ha : a < 0) (hb : b < 0) : a + b < 0 :=
  Int.zero_add 0 ▸ Int.add_lt_add ha hb

protected theorem add_neg_of_neg_of_nonpos {a b : Int} (ha : a < 0) (hb : b ≤ 0) : a + b < 0 :=
  Int.zero_add 0 ▸ Int.add_lt_add_of_lt_of_le ha hb

protected theorem add_neg_of_nonpos_of_neg {a b : Int} (ha : a ≤ 0) (hb : b < 0) : a + b < 0 :=
  Int.zero_add 0 ▸ Int.add_lt_add_of_le_of_lt ha hb

protected theorem lt_add_of_le_of_pos {a b c : Int} (hbc : b ≤ c) (ha : 0 < a) : b < c + a :=
  Int.add_zero b ▸ Int.add_lt_add_of_le_of_lt hbc ha

theorem add_one_le_iff {a b : Int} : a + 1 ≤ b ↔ a < b := .rfl

theorem lt_add_one_iff {a b : Int} : a < b + 1 ↔ a ≤ b := Int.add_le_add_iff_right _

@[simp] theorem succ_ofNat_pos (n : Nat) : 0 < (n : Int) + 1 :=
  lt_add_one_iff.2 (ofNat_zero_le _)

theorem le_add_one {a b : Int} (h : a ≤ b) : a ≤ b + 1 :=
  Int.le_of_lt (Int.lt_add_one_iff.2 h)

protected theorem neg_le_neg {a b : Int} (h : a ≤ b) : -b ≤ -a := by
  have : 0 ≤ -a + b := Int.add_left_neg a ▸ Int.add_le_add_left h (-a)
  have : 0 + -b ≤ -a + b + -b := Int.add_le_add_right this (-b)
  rwa [Int.add_neg_cancel_right, Int.zero_add] at this

protected theorem le_of_neg_le_neg {a b : Int} (h : -b ≤ -a) : a ≤ b :=
  suffices - -a ≤ - -b by simp [Int.neg_neg] at this; assumption
  Int.neg_le_neg h

protected theorem nonneg_of_neg_nonpos {a : Int} (h : -a ≤ 0) : 0 ≤ a :=
  Int.le_of_neg_le_neg <| by rwa [Int.neg_zero]

protected theorem neg_nonpos_of_nonneg {a : Int} (h : 0 ≤ a) : -a ≤ 0 := by
  have : -a ≤ -0 := Int.neg_le_neg h
  rwa [Int.neg_zero] at this

protected theorem nonpos_of_neg_nonneg {a : Int} (h : 0 ≤ -a) : a ≤ 0 :=
  Int.le_of_neg_le_neg <| by rwa [Int.neg_zero]

protected theorem neg_nonneg_of_nonpos {a : Int} (h : a ≤ 0) : 0 ≤ -a := by
  have : -0 ≤ -a := Int.neg_le_neg h
  rwa [Int.neg_zero] at this

protected theorem neg_lt_neg {a b : Int} (h : a < b) : -b < -a := by
  have : 0 < -a + b := Int.add_left_neg a ▸ Int.add_lt_add_left h (-a)
  have : 0 + -b < -a + b + -b := Int.add_lt_add_right this (-b)
  rwa [Int.add_neg_cancel_right, Int.zero_add] at this

protected theorem lt_of_neg_lt_neg {a b : Int} (h : -b < -a) : a < b :=
  Int.neg_neg a ▸ Int.neg_neg b ▸ Int.neg_lt_neg h

protected theorem pos_of_neg_neg {a : Int} (h : -a < 0) : 0 < a :=
  Int.lt_of_neg_lt_neg <| by rwa [Int.neg_zero]

protected theorem neg_neg_of_pos {a : Int} (h : 0 < a) : -a < 0 := by
  have : -a < -0 := Int.neg_lt_neg h
  rwa [Int.neg_zero] at this

protected theorem neg_of_neg_pos {a : Int} (h : 0 < -a) : a < 0 :=
  have : -0 < -a := by rwa [Int.neg_zero]
  Int.lt_of_neg_lt_neg this

protected theorem neg_pos_of_neg {a : Int} (h : a < 0) : 0 < -a := by
  have : -0 < -a := Int.neg_lt_neg h
  rwa [Int.neg_zero] at this

protected theorem le_neg_of_le_neg {a b : Int} (h : a ≤ -b) : b ≤ -a := by
  have h := Int.neg_le_neg h
  rwa [Int.neg_neg] at h

protected theorem neg_le_of_neg_le {a b : Int} (h : -a ≤ b) : -b ≤ a := by
  have h := Int.neg_le_neg h
  rwa [Int.neg_neg] at h

protected theorem lt_neg_of_lt_neg {a b : Int} (h : a < -b) : b < -a := by
  have h := Int.neg_lt_neg h
  rwa [Int.neg_neg] at h

protected theorem neg_lt_of_neg_lt {a b : Int} (h : -a < b) : -b < a := by
  have h := Int.neg_lt_neg h
  rwa [Int.neg_neg] at h

protected theorem sub_nonneg_of_le {a b : Int} (h : b ≤ a) : 0 ≤ a - b := by
  have h := Int.add_le_add_right h (-b)
  rwa [Int.add_right_neg] at h

protected theorem le_of_sub_nonneg {a b : Int} (h : 0 ≤ a - b) : b ≤ a := by
  have h := Int.add_le_add_right h b
  rwa [Int.sub_add_cancel, Int.zero_add] at h

protected theorem sub_nonpos_of_le {a b : Int} (h : a ≤ b) : a - b ≤ 0 := by
  have h := Int.add_le_add_right h (-b)
  rwa [Int.add_right_neg] at h

protected theorem le_of_sub_nonpos {a b : Int} (h : a - b ≤ 0) : a ≤ b := by
  have h := Int.add_le_add_right h b
  rwa [Int.sub_add_cancel, Int.zero_add] at h

protected theorem sub_pos_of_lt {a b : Int} (h : b < a) : 0 < a - b := by
  have h := Int.add_lt_add_right h (-b)
  rwa [Int.add_right_neg] at h

protected theorem lt_of_sub_pos {a b : Int} (h : 0 < a - b) : b < a := by
  have h := Int.add_lt_add_right h b
  rwa [Int.sub_add_cancel, Int.zero_add] at h

protected theorem sub_neg_of_lt {a b : Int} (h : a < b) : a - b < 0 := by
  have h := Int.add_lt_add_right h (-b)
  rwa [Int.add_right_neg] at h

protected theorem lt_of_sub_neg {a b : Int} (h : a - b < 0) : a < b := by
  have h := Int.add_lt_add_right h b
  rwa [Int.sub_add_cancel, Int.zero_add] at h

protected theorem add_le_of_le_neg_add {a b c : Int} (h : b ≤ -a + c) : a + b ≤ c := by
  have h := Int.add_le_add_left h a
  rwa [Int.add_neg_cancel_left] at h

protected theorem le_neg_add_of_add_le {a b c : Int} (h : a + b ≤ c) : b ≤ -a + c := by
  have h := Int.add_le_add_left h (-a)
  rwa [Int.neg_add_cancel_left] at h

protected theorem add_le_of_le_sub_left {a b c : Int} (h : b ≤ c - a) : a + b ≤ c := by
  have h := Int.add_le_add_left h a
  rwa [← Int.add_sub_assoc, Int.add_comm a c, Int.add_sub_cancel] at h

protected theorem le_sub_left_of_add_le {a b c : Int} (h : a + b ≤ c) : b ≤ c - a := by
  have h := Int.add_le_add_right h (-a)
  rwa [Int.add_comm a b, Int.add_neg_cancel_right] at h

protected theorem add_le_of_le_sub_right {a b c : Int} (h : a ≤ c - b) : a + b ≤ c := by
  have h := Int.add_le_add_right h b
  rwa [Int.sub_add_cancel] at h

protected theorem le_sub_right_of_add_le {a b c : Int} (h : a + b ≤ c) : a ≤ c - b := by
  have h := Int.add_le_add_right h (-b)
  rwa [Int.add_neg_cancel_right] at h

protected theorem le_add_of_neg_add_le {a b c : Int} (h : -b + a ≤ c) : a ≤ b + c := by
  have h := Int.add_le_add_left h b
  rwa [Int.add_neg_cancel_left] at h

protected theorem neg_add_le_of_le_add {a b c : Int} (h : a ≤ b + c) : -b + a ≤ c := by
  have h := Int.add_le_add_left h (-b)
  rwa [Int.neg_add_cancel_left] at h

protected theorem le_add_of_sub_left_le {a b c : Int} (h : a - b ≤ c) : a ≤ b + c := by
  have h := Int.add_le_add_right h b
  rwa [Int.sub_add_cancel, Int.add_comm] at h

protected theorem sub_left_le_of_le_add {a b c : Int} (h : a ≤ b + c) : a - b ≤ c := by
  have h := Int.add_le_add_right h (-b)
  rwa [Int.add_comm b c, Int.add_neg_cancel_right] at h

protected theorem le_add_of_sub_right_le {a b c : Int} (h : a - c ≤ b) : a ≤ b + c := by
  have h := Int.add_le_add_right h c
  rwa [Int.sub_add_cancel] at h

protected theorem sub_right_le_of_le_add {a b c : Int} (h : a ≤ b + c) : a - c ≤ b := by
  have h := Int.add_le_add_right h (-c)
  rwa [Int.add_neg_cancel_right] at h

protected theorem le_add_of_neg_add_le_left {a b c : Int} (h : -b + a ≤ c) : a ≤ b + c := by
  rw [Int.add_comm] at h
  exact Int.le_add_of_sub_left_le h

protected theorem neg_add_le_left_of_le_add {a b c : Int} (h : a ≤ b + c) : -b + a ≤ c := by
  rw [Int.add_comm]
  exact Int.sub_left_le_of_le_add h

protected theorem le_add_of_neg_add_le_right {a b c : Int} (h : -c + a ≤ b) : a ≤ b + c := by
  rw [Int.add_comm] at h
  exact Int.le_add_of_sub_right_le h

protected theorem neg_add_le_right_of_le_add {a b c : Int} (h : a ≤ b + c) : -c + a ≤ b := by
  rw [Int.add_comm] at h
  exact Int.neg_add_le_left_of_le_add h

protected theorem le_add_of_neg_le_sub_left {a b c : Int} (h : -a ≤ b - c) : c ≤ a + b :=
  Int.le_add_of_neg_add_le_left (Int.add_le_of_le_sub_right h)

protected theorem neg_le_sub_left_of_le_add {a b c : Int} (h : c ≤ a + b) : -a ≤ b - c := by
  have h := Int.le_neg_add_of_add_le (Int.sub_left_le_of_le_add h)
  rwa [Int.add_comm] at h

protected theorem le_add_of_neg_le_sub_right {a b c : Int} (h : -b ≤ a - c) : c ≤ a + b :=
  Int.le_add_of_sub_right_le (Int.add_le_of_le_sub_left h)

protected theorem neg_le_sub_right_of_le_add {a b c : Int} (h : c ≤ a + b) : -b ≤ a - c :=
  Int.le_sub_left_of_add_le (Int.sub_right_le_of_le_add h)

protected theorem sub_le_of_sub_le {a b c : Int} (h : a - b ≤ c) : a - c ≤ b :=
  Int.sub_left_le_of_le_add (Int.le_add_of_sub_right_le h)

protected theorem sub_le_sub_left {a b : Int} (h : a ≤ b) (c : Int) : c - b ≤ c - a :=
  Int.add_le_add_left (Int.neg_le_neg h) c

protected theorem sub_le_sub_right {a b : Int} (h : a ≤ b) (c : Int) : a - c ≤ b - c :=
  Int.add_le_add_right h (-c)

protected theorem sub_le_sub {a b c d : Int} (hab : a ≤ b) (hcd : c ≤ d) : a - d ≤ b - c :=
  Int.add_le_add hab (Int.neg_le_neg hcd)

protected theorem add_lt_of_lt_neg_add {a b c : Int} (h : b < -a + c) : a + b < c := by
  have h := Int.add_lt_add_left h a
  rwa [Int.add_neg_cancel_left] at h

protected theorem lt_neg_add_of_add_lt {a b c : Int} (h : a + b < c) : b < -a + c := by
  have h := Int.add_lt_add_left h (-a)
  rwa [Int.neg_add_cancel_left] at h

protected theorem add_lt_of_lt_sub_left {a b c : Int} (h : b < c - a) : a + b < c := by
  have h := Int.add_lt_add_left h a
  rwa [← Int.add_sub_assoc, Int.add_comm a c, Int.add_sub_cancel] at h

protected theorem lt_sub_left_of_add_lt {a b c : Int} (h : a + b < c) : b < c - a := by
  have h := Int.add_lt_add_right h (-a)
  rwa [Int.add_comm a b, Int.add_neg_cancel_right] at h

protected theorem add_lt_of_lt_sub_right {a b c : Int} (h : a < c - b) : a + b < c := by
  have h := Int.add_lt_add_right h b
  rwa [Int.sub_add_cancel] at h

protected theorem lt_sub_right_of_add_lt {a b c : Int} (h : a + b < c) : a < c - b := by
  have h := Int.add_lt_add_right h (-b)
  rwa [Int.add_neg_cancel_right] at h

protected theorem lt_add_of_neg_add_lt {a b c : Int} (h : -b + a < c) : a < b + c := by
  have h := Int.add_lt_add_left h b
  rwa [Int.add_neg_cancel_left] at h

protected theorem neg_add_lt_of_lt_add {a b c : Int} (h : a < b + c) : -b + a < c := by
  have h := Int.add_lt_add_left h (-b)
  rwa [Int.neg_add_cancel_left] at h

protected theorem lt_add_of_sub_left_lt {a b c : Int} (h : a - b < c) : a < b + c := by
  have h := Int.add_lt_add_right h b
  rwa [Int.sub_add_cancel, Int.add_comm] at h

protected theorem sub_left_lt_of_lt_add {a b c : Int} (h : a < b + c) : a - b < c := by
  have h := Int.add_lt_add_right h (-b)
  rwa [Int.add_comm b c, Int.add_neg_cancel_right] at h

protected theorem lt_add_of_sub_right_lt {a b c : Int} (h : a - c < b) : a < b + c := by
  have h := Int.add_lt_add_right h c
  rwa [Int.sub_add_cancel] at h

protected theorem sub_right_lt_of_lt_add {a b c : Int} (h : a < b + c) : a - c < b := by
  have h := Int.add_lt_add_right h (-c)
  rwa [Int.add_neg_cancel_right] at h

protected theorem lt_add_of_neg_add_lt_left {a b c : Int} (h : -b + a < c) : a < b + c := by
  rw [Int.add_comm] at h
  exact Int.lt_add_of_sub_left_lt h

protected theorem neg_add_lt_left_of_lt_add {a b c : Int} (h : a < b + c) : -b + a < c := by
  rw [Int.add_comm]
  exact Int.sub_left_lt_of_lt_add h

protected theorem lt_add_of_neg_add_lt_right {a b c : Int} (h : -c + a < b) : a < b + c := by
  rw [Int.add_comm] at h
  exact Int.lt_add_of_sub_right_lt h

protected theorem neg_add_lt_right_of_lt_add {a b c : Int} (h : a < b + c) : -c + a < b := by
  rw [Int.add_comm] at h
  exact Int.neg_add_lt_left_of_lt_add h

protected theorem lt_add_of_neg_lt_sub_left {a b c : Int} (h : -a < b - c) : c < a + b :=
  Int.lt_add_of_neg_add_lt_left (Int.add_lt_of_lt_sub_right h)

protected theorem neg_lt_sub_left_of_lt_add {a b c : Int} (h : c < a + b) : -a < b - c := by
  have h := Int.lt_neg_add_of_add_lt (Int.sub_left_lt_of_lt_add h)
  rwa [Int.add_comm] at h

protected theorem lt_add_of_neg_lt_sub_right {a b c : Int} (h : -b < a - c) : c < a + b :=
  Int.lt_add_of_sub_right_lt (Int.add_lt_of_lt_sub_left h)

protected theorem neg_lt_sub_right_of_lt_add {a b c : Int} (h : c < a + b) : -b < a - c :=
  Int.lt_sub_left_of_add_lt (Int.sub_right_lt_of_lt_add h)

protected theorem sub_lt_of_sub_lt {a b c : Int} (h : a - b < c) : a - c < b :=
  Int.sub_left_lt_of_lt_add (Int.lt_add_of_sub_right_lt h)

protected theorem sub_lt_sub_left {a b : Int} (h : a < b) (c : Int) : c - b < c - a :=
  Int.add_lt_add_left (Int.neg_lt_neg h) c

protected theorem sub_lt_sub_right {a b : Int} (h : a < b) (c : Int) : a - c < b - c :=
  Int.add_lt_add_right h (-c)

protected theorem sub_lt_sub {a b c d : Int} (hab : a < b) (hcd : c < d) : a - d < b - c :=
  Int.add_lt_add hab (Int.neg_lt_neg hcd)

protected theorem sub_lt_sub_of_le_of_lt {a b c d : Int}
  (hab : a ≤ b) (hcd : c < d) : a - d < b - c :=
  Int.add_lt_add_of_le_of_lt hab (Int.neg_lt_neg hcd)

protected theorem sub_lt_sub_of_lt_of_le {a b c d : Int}
  (hab : a < b) (hcd : c ≤ d) : a - d < b - c :=
  Int.add_lt_add_of_lt_of_le hab (Int.neg_le_neg hcd)

protected theorem sub_le_self (a : Int) {b : Int} (h : 0 ≤ b) : a - b ≤ a :=
  calc  a + -b
    _ ≤ a + 0 := Int.add_le_add_left (Int.neg_nonpos_of_nonneg h) _
    _ = a     := by rw [Int.add_zero]

protected theorem sub_lt_self (a : Int) {b : Int} (h : 0 < b) : a - b < a :=
  calc  a + -b
    _ < a + 0 := Int.add_lt_add_left (Int.neg_neg_of_pos h) _
    _ = a     := by rw [Int.add_zero]

protected theorem add_le_add_three {a b c d e f : Int}
    (h₁ : a ≤ d) (h₂ : b ≤ e) (h₃ : c ≤ f) : a + b + c ≤ d + e + f :=
  Int.add_le_add (Int.add_le_add h₁ h₂) h₃

protected theorem mul_lt_mul_of_pos_left {a b c : Int}
  (h₁ : a < b) (h₂ : 0 < c) : c * a < c * b := by
  have : 0 < c * (b - a) := Int.mul_pos h₂ (Int.sub_pos_of_lt h₁)
  rw [Int.mul_sub] at this
  exact Int.lt_of_sub_pos this

protected theorem mul_lt_mul_of_pos_right {a b c : Int}
  (h₁ : a < b) (h₂ : 0 < c) : a * c < b * c := by
  have : 0 < b - a := Int.sub_pos_of_lt h₁
  have : 0 < (b - a) * c := Int.mul_pos this h₂
  rw [Int.sub_mul] at this
  exact Int.lt_of_sub_pos this

protected theorem mul_le_mul_of_nonneg_left {a b c : Int}
    (h₁ : a ≤ b) (h₂ : 0 ≤ c) : c * a ≤ c * b := by
  if hba : b ≤ a then rw [Int.le_antisymm hba h₁]; apply Int.le_refl else
  if hc0 : c ≤ 0 then simp [Int.le_antisymm hc0 h₂, Int.zero_mul] else
  exact Int.le_of_lt <| Int.mul_lt_mul_of_pos_left
    (Int.lt_iff_le_not_le.2 ⟨h₁, hba⟩) (Int.lt_iff_le_not_le.2 ⟨h₂, hc0⟩)

protected theorem mul_le_mul_of_nonneg_right {a b c : Int}
    (h₁ : a ≤ b) (h₂ : 0 ≤ c) : a * c ≤ b * c := by
  rw [Int.mul_comm, Int.mul_comm b]; exact Int.mul_le_mul_of_nonneg_left h₁ h₂

protected theorem mul_le_mul {a b c d : Int}
    (hac : a ≤ c) (hbd : b ≤ d) (nn_b : 0 ≤ b) (nn_c : 0 ≤ c) : a * b ≤ c * d :=
  Int.le_trans (Int.mul_le_mul_of_nonneg_right hac nn_b) (Int.mul_le_mul_of_nonneg_left hbd nn_c)

protected theorem mul_nonpos_of_nonneg_of_nonpos {a b : Int}
  (ha : 0 ≤ a) (hb : b ≤ 0) : a * b ≤ 0 := by
  have h : a * b ≤ a * 0 := Int.mul_le_mul_of_nonneg_left hb ha
  rwa [Int.mul_zero] at h

protected theorem mul_nonpos_of_nonpos_of_nonneg {a b : Int}
  (ha : a ≤ 0) (hb : 0 ≤ b) : a * b ≤ 0 := by
  have h : a * b ≤ 0 * b := Int.mul_le_mul_of_nonneg_right ha hb
  rwa [Int.zero_mul] at h

protected theorem mul_lt_mul {a b c d : Int}
    (h₁ : a < c) (h₂ : b ≤ d) (h₃ : 0 < b) (h₄ : 0 ≤ c) : a * b < c * d :=
  Int.lt_of_lt_of_le (Int.mul_lt_mul_of_pos_right h₁ h₃) (Int.mul_le_mul_of_nonneg_left h₂ h₄)

protected theorem mul_lt_mul' {a b c d : Int}
    (h₁ : a ≤ c) (h₂ : b < d) (h₃ : 0 ≤ b) (h₄ : 0 < c) : a * b < c * d :=
  Int.lt_of_le_of_lt (Int.mul_le_mul_of_nonneg_right h₁ h₃) (Int.mul_lt_mul_of_pos_left h₂ h₄)

protected theorem mul_neg_of_pos_of_neg {a b : Int} (ha : 0 < a) (hb : b < 0) : a * b < 0 := by
  have h : a * b < a * 0 := Int.mul_lt_mul_of_pos_left hb ha
  rwa [Int.mul_zero] at h

protected theorem mul_neg_of_neg_of_pos {a b : Int} (ha : a < 0) (hb : 0 < b) : a * b < 0 := by
  have h : a * b < 0 * b := Int.mul_lt_mul_of_pos_right ha hb
  rwa [Int.zero_mul] at h

protected theorem mul_le_mul_of_nonpos_right {a b c : Int}
    (h : b ≤ a) (hc : c ≤ 0) : a * c ≤ b * c :=
  have : -c ≥ 0 := Int.neg_nonneg_of_nonpos hc
  have : b * -c ≤ a * -c := Int.mul_le_mul_of_nonneg_right h this
  Int.le_of_neg_le_neg <| by rwa [← Int.neg_mul_eq_mul_neg, ← Int.neg_mul_eq_mul_neg] at this

protected theorem mul_nonneg_of_nonpos_of_nonpos {a b : Int}
  (ha : a ≤ 0) (hb : b ≤ 0) : 0 ≤ a * b := by
  have : 0 * b ≤ a * b := Int.mul_le_mul_of_nonpos_right ha hb
  rwa [Int.zero_mul] at this

protected theorem mul_lt_mul_of_neg_left {a b c : Int} (h : b < a) (hc : c < 0) : c * a < c * b :=
  have : -c > 0 := Int.neg_pos_of_neg hc
  have : -c * b < -c * a := Int.mul_lt_mul_of_pos_left h this
  have : -(c * b) < -(c * a) := by
    rwa [← Int.neg_mul_eq_neg_mul, ← Int.neg_mul_eq_neg_mul] at this
  Int.lt_of_neg_lt_neg this

protected theorem mul_lt_mul_of_neg_right {a b c : Int} (h : b < a) (hc : c < 0) : a * c < b * c :=
  have : -c > 0 := Int.neg_pos_of_neg hc
  have : b * -c < a * -c := Int.mul_lt_mul_of_pos_right h this
  have : -(b * c) < -(a * c) := by
    rwa [← Int.neg_mul_eq_mul_neg, ← Int.neg_mul_eq_mul_neg] at this
  Int.lt_of_neg_lt_neg this

protected theorem mul_pos_of_neg_of_neg {a b : Int} (ha : a < 0) (hb : b < 0) : 0 < a * b := by
  have : 0 * b < a * b := Int.mul_lt_mul_of_neg_right ha hb
  rwa [Int.zero_mul] at this

protected theorem mul_self_le_mul_self {a b : Int} (h1 : 0 ≤ a) (h2 : a ≤ b) : a * a ≤ b * b :=
  Int.mul_le_mul h2 h2 h1 (Int.le_trans h1 h2)

protected theorem mul_self_lt_mul_self {a b : Int} (h1 : 0 ≤ a) (h2 : a < b) : a * a < b * b :=
  Int.mul_lt_mul' (Int.le_of_lt h2) h2 h1 (Int.lt_of_le_of_lt h1 h2)

theorem exists_eq_neg_ofNat {a : Int} (H : a ≤ 0) : ∃ n : Nat, a = -(n : Int) :=
  let ⟨n, h⟩ := eq_ofNat_of_zero_le (Int.neg_nonneg_of_nonpos H)
  ⟨n, Int.eq_neg_of_eq_neg h.symm⟩

theorem natAbs_of_nonneg {a : Int} (H : 0 ≤ a) : (natAbs a : Int) = a :=
  match a, eq_ofNat_of_zero_le H with
  | _, ⟨_, rfl⟩ => rfl

theorem ofNat_natAbs_of_nonpos {a : Int} (H : a ≤ 0) : (natAbs a : Int) = -a := by
  rw [← natAbs_neg, natAbs_of_nonneg (Int.neg_nonneg_of_nonpos H)]

theorem lt_of_add_one_le {a b : Int} (H : a + 1 ≤ b) : a < b := H

theorem add_one_le_of_lt {a b : Int} (H : a < b) : a + 1 ≤ b := H

theorem lt_add_one_of_le {a b : Int} (H : a ≤ b) : a < b + 1 := Int.add_le_add_right H 1

theorem le_of_lt_add_one {a b : Int} (H : a < b + 1) : a ≤ b := Int.le_of_add_le_add_right H

theorem sub_one_lt_of_le {a b : Int} (H : a ≤ b) : a - 1 < b :=
  Int.sub_right_lt_of_lt_add <| lt_add_one_of_le H

theorem le_of_sub_one_lt {a b : Int} (H : a - 1 < b) : a ≤ b :=
  le_of_lt_add_one <| Int.lt_add_of_sub_right_lt H

theorem le_sub_one_of_lt {a b : Int} (H : a < b) : a ≤ b - 1 := Int.le_sub_right_of_add_le H

theorem lt_of_le_sub_one {a b : Int} (H : a ≤ b - 1) : a < b := Int.add_le_of_le_sub_right H

theorem sign_eq_one_of_pos {a : Int} (h : 0 < a) : sign a = 1 :=
  match a, eq_succ_of_zero_lt h with
  | _, ⟨_, rfl⟩ => rfl

theorem sign_eq_neg_one_of_neg {a : Int} (h : a < 0) : sign a = -1 :=
  match a, eq_negSucc_of_lt_zero h with
  | _, ⟨_, rfl⟩ => rfl

theorem eq_zero_of_sign_eq_zero : ∀ {a : Int}, sign a = 0 → a = 0
  | 0, _ => rfl

theorem pos_of_sign_eq_one : ∀ {a : Int}, sign a = 1 → 0 < a
  | (_ + 1 : Nat), _ => ofNat_lt.2 (Nat.succ_pos _)

theorem neg_of_sign_eq_neg_one : ∀ {a : Int}, sign a = -1 → a < 0
  | (_ + 1 : Nat), h => nomatch h
  | 0, h => nomatch h
  | -[_+1], _ => negSucc_lt_zero _

theorem sign_eq_one_iff_pos (a : Int) : sign a = 1 ↔ 0 < a :=
  ⟨pos_of_sign_eq_one, sign_eq_one_of_pos⟩

theorem sign_eq_neg_one_iff_neg (a : Int) : sign a = -1 ↔ a < 0 :=
  ⟨neg_of_sign_eq_neg_one, sign_eq_neg_one_of_neg⟩

theorem sign_eq_zero_iff_zero (a : Int) : sign a = 0 ↔ a = 0 :=
  ⟨eq_zero_of_sign_eq_zero, fun h => by rw [h, sign_zero]⟩

protected theorem mul_eq_zero {a b : Int} : a * b = 0 ↔ a = 0 ∨ b = 0 := by
  refine ⟨fun h => ?_, fun h => h.elim (by simp [·, Int.zero_mul]) (by simp [·, Int.mul_zero])⟩
  exact match Int.lt_trichotomy a 0, Int.lt_trichotomy b 0 with
  | .inr (.inl heq₁), _ => .inl heq₁
  | _, .inr (.inl heq₂) => .inr heq₂
  | .inl hlt₁, .inl hlt₂ => absurd h <| Int.ne_of_gt <| Int.mul_pos_of_neg_of_neg hlt₁ hlt₂
  | .inl hlt₁, .inr (.inr hgt₂) => absurd h <| Int.ne_of_lt <| Int.mul_neg_of_neg_of_pos hlt₁ hgt₂
  | .inr (.inr hgt₁), .inl hlt₂ => absurd h <| Int.ne_of_lt <| Int.mul_neg_of_pos_of_neg hgt₁ hlt₂
  | .inr (.inr hgt₁), .inr (.inr hgt₂) => absurd h <| Int.ne_of_gt <| Int.mul_pos hgt₁ hgt₂

protected theorem mul_ne_zero {a b : Int} (a0 : a ≠ 0) (b0 : b ≠ 0) : a * b ≠ 0 :=
  mt Int.mul_eq_zero.1 <| not_or.2 ⟨a0, b0⟩

protected theorem eq_of_mul_eq_mul_right {a b c : Int} (ha : a ≠ 0) (h : b * a = c * a) : b = c :=
  have : (b - c) * a = 0 := by rwa [Int.sub_mul, Int.sub_eq_zero]
  Int.sub_eq_zero.1 <| (Int.mul_eq_zero.1 this).resolve_right ha

protected theorem eq_of_mul_eq_mul_left {a b c : Int} (ha : a ≠ 0) (h : a * b = a * c) : b = c :=
  have : a * b - a * c = 0 := Int.sub_eq_zero_of_eq h
  have : a * (b - c) = 0 := by rw [Int.mul_sub, this]
  have : b - c = 0 := (Int.mul_eq_zero.1 this).resolve_left ha
  Int.eq_of_sub_eq_zero this

theorem mul_eq_mul_left_iff {a b c : Int} (h : c ≠ 0) : c * a = c * b ↔ a = b :=
  ⟨Int.eq_of_mul_eq_mul_left h, fun w => congrArg (fun x => c * x) w⟩

theorem mul_eq_mul_right_iff {a b c : Int} (h : c ≠ 0) : a * c = b * c ↔ a = b :=
  ⟨Int.eq_of_mul_eq_mul_right h, fun w => congrArg (fun x => x * c) w⟩

theorem eq_one_of_mul_eq_self_left {a b : Int} (Hpos : a ≠ 0) (H : b * a = a) : b = 1 :=
  Int.eq_of_mul_eq_mul_right Hpos <| by rw [Int.one_mul, H]

theorem eq_one_of_mul_eq_self_right {a b : Int} (Hpos : b ≠ 0) (H : b * a = b) : a = 1 :=
  Int.eq_of_mul_eq_mul_left Hpos <| by rw [Int.mul_one, H]

/-! ### nat abs -/

theorem ofNat_natAbs_eq_of_nonneg : ∀ a : Int, 0 ≤ a → Int.natAbs a = a
  | (_:Nat), _ => rfl
  | -[n+1],  h => absurd (negSucc_lt_zero n) (Int.not_lt.2 h)

theorem eq_natAbs_iff_mul_eq_zero : natAbs a = n ↔ (a - n) * (a + n) = 0 := by
  rw [natAbs_eq_iff, Int.mul_eq_zero, ← Int.sub_neg, Int.sub_eq_zero, Int.sub_eq_zero]

theorem natAbs_add_le (a b : Int) : natAbs (a + b) ≤ natAbs a + natAbs b := by
  suffices ∀ a b : Nat, natAbs (subNatNat a b.succ) ≤ (a + b).succ by
    match a, b with
    | (a:Nat), (b:Nat) => simp
    | (a:Nat), -[b+1]  => simp; apply this
    | -[a+1],  (b:Nat) => simp [Nat.succ_add, Nat.add_comm a b]; apply this
    | -[a+1],  -[b+1]  => simp [Nat.succ_add]; apply Nat.le_refl
  refine fun a b => subNatNat_elim a b.succ
    (fun m n i => n = b.succ → natAbs i ≤ (m + b).succ) ?_
    (fun i n (e : (n + i).succ = _) => ?_) rfl
  · rintro i n rfl
    rw [Nat.add_comm _ i, Nat.add_assoc]
    exact Nat.le_add_right i (b.succ + b).succ
  · apply succ_le_succ
    rw [← succ.inj e, ← Nat.add_assoc, Nat.add_comm]
    apply Nat.le_add_right

theorem natAbs_sub_le (a b : Int) : natAbs (a - b) ≤ natAbs a + natAbs b := by
  rw [← Int.natAbs_neg b]; apply natAbs_add_le

theorem negSucc_eq' (m : Nat) : -[m+1] = -m - 1 := by simp only [negSucc_eq, Int.neg_add]; rfl

theorem natAbs_lt_natAbs_of_nonneg_of_lt {a b : Int}
    (w₁ : 0 ≤ a) (w₂ : a < b) : a.natAbs < b.natAbs :=
  match a, b, eq_ofNat_of_zero_le w₁, eq_ofNat_of_zero_le (Int.le_trans w₁ (Int.le_of_lt w₂)) with
  | _, _, ⟨_, rfl⟩, ⟨_, rfl⟩ => ofNat_lt.1 w₂

/-! ### toNat -/

theorem toNat_eq_max : ∀ a : Int, (toNat a : Int) = max a 0
  | (n : Nat) => (Int.max_eq_left (ofNat_zero_le n)).symm
  | -[n+1] => (Int.max_eq_right (Int.le_of_lt (negSucc_lt_zero n))).symm

@[simp] theorem toNat_zero : (0 : Int).toNat = 0 := rfl

@[simp] theorem toNat_one : (1 : Int).toNat = 1 := rfl

@[simp] theorem toNat_of_nonneg {a : Int} (h : 0 ≤ a) : (toNat a : Int) = a := by
  rw [toNat_eq_max, Int.max_eq_left h]

@[simp] theorem toNat_ofNat (n : Nat) : toNat ↑n = n := rfl

@[simp] theorem toNat_ofNat_add_one {n : Nat} : ((n : Int) + 1).toNat = n + 1 := rfl

theorem self_le_toNat (a : Int) : a ≤ toNat a := by rw [toNat_eq_max]; apply Int.le_max_left

@[simp] theorem le_toNat {n : Nat} {z : Int} (h : 0 ≤ z) : n ≤ z.toNat ↔ (n : Int) ≤ z := by
  rw [← Int.ofNat_le, Int.toNat_of_nonneg h]

@[simp] theorem toNat_lt {n : Nat} {z : Int} (h : 0 ≤ z) : z.toNat < n ↔ z < (n : Int) := by
  rw [← Int.not_le, ← Nat.not_le, Int.le_toNat h]

theorem toNat_add {a b : Int} (ha : 0 ≤ a) (hb : 0 ≤ b) : (a + b).toNat = a.toNat + b.toNat :=
  match a, b, eq_ofNat_of_zero_le ha, eq_ofNat_of_zero_le hb with
  | _, _, ⟨_, rfl⟩, ⟨_, rfl⟩ => rfl

theorem toNat_add_nat {a : Int} (ha : 0 ≤ a) (n : Nat) : (a + n).toNat = a.toNat + n :=
  match a, eq_ofNat_of_zero_le ha with | _, ⟨_, rfl⟩ => rfl

@[simp] theorem pred_toNat : ∀ i : Int, (i - 1).toNat = i.toNat - 1
  | 0 => rfl
  | (n+1:Nat) => by simp [ofNat_add]
  | -[n+1] => rfl

@[simp] theorem toNat_sub_toNat_neg : ∀ n : Int, ↑n.toNat - ↑(-n).toNat = n
  | 0 => rfl
  | (_+1:Nat) => Int.sub_zero _
  | -[_+1] => Int.zero_sub _

@[simp] theorem toNat_add_toNat_neg_eq_natAbs : ∀ n : Int, n.toNat + (-n).toNat = n.natAbs
  | 0 => rfl
  | (_+1:Nat) => Nat.add_zero _
  | -[_+1] => Nat.zero_add _

theorem mem_toNat' : ∀ (a : Int) (n : Nat), toNat' a = some n ↔ a = n
  | (m : Nat), n => Option.some_inj.trans ofNat_inj.symm
  | -[m+1], n => by constructor <;> intro.

@[simp] theorem toNat_neg_nat : ∀ n : Nat, (-(n : Int)).toNat = 0
  | 0 => rfl
  | _+1 => rfl

/-!
The following lemmas are later subsumed by e.g. `Nat.cast_add` and `Nat.cast_mul` in Mathlib
but it is convenient to have these earlier, for users who only need `Nat` and `Int`.
-/

theorem natCast_zero : ((0 : Nat) : Int) = (0 : Int) := rfl

theorem natCast_one : ((1 : Nat) : Int) = (1 : Int) := rfl

@[simp] theorem natCast_add (a b : Nat) : ((a + b : Nat) : Int) = (a : Int) + (b : Int) := by
  -- Note this only works because of local simp attributes in this file,
  -- so it still makes sense to tag the lemmas with `@[simp]`.
  simp

@[simp] theorem natCast_mul (a b : Nat) : ((a * b : Nat) : Int) = (a : Int) * (b : Int) := by
  simp

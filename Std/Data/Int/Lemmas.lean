/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Deniz Aydin, Floris van Doorn, Mario Carneiro
-/
import Std.Data.Nat.Lemmas
import Std.Data.Int.Basic

open Nat

namespace Int

theorem ofNat_zero : ofNat 0 = 0 := rfl

theorem ofNat_one  : ofNat 1 = 1 := rfl

/- ## Definitions of basic functions -/

theorem subNatNat_of_sub_eq_zero {m n : Nat} (h : n - m = 0) : subNatNat m n = ofNat (m - n) := by
  rw [subNatNat, h]

theorem subNatNat_of_sub_eq_succ {m n k : Nat} (h : n - m = succ k) : subNatNat m n = -[k+1] := by
  rw [subNatNat, h]

protected theorem neg_zero : -(0:Int) = 0 := rfl

theorem ofNat_add (n m : Nat) : ofNat (n + m) = ofNat n + ofNat m := rfl
theorem ofNat_mul (n m : Nat) : ofNat (n * m) = ofNat n * ofNat m := rfl
theorem ofNat_succ (n : Nat) : ofNat (succ n) = ofNat n + 1 := rfl

@[local simp] theorem neg_ofNat_zero : -ofNat 0 = 0 := rfl
@[local simp] theorem neg_ofNat_of_succ (n : Nat) : -ofNat (succ n) = -[n+1] := rfl
@[local simp] theorem neg_neg_ofNat_succ (n : Nat) : -(-[n+1]) = ofNat (succ n) := rfl

theorem negSucc_ofNat_coe (n : Nat) : -[n+1] = -↑(n + 1) := rfl

/- ## These are only for internal use -/

@[local simp] theorem ofNat_add_ofNat (m n : Nat) :
    ofNat m + ofNat n = ofNat (m + n) := rfl
@[local simp] theorem ofNat_add_negSucc_ofNat (m n : Nat) :
    ofNat m + -[n+1] = subNatNat m (succ n) := rfl
@[local simp] theorem negSucc_ofNat_add_ofNat (m n : Nat) :
    -[m+1] + ofNat n = subNatNat n (succ m) := rfl
@[local simp] theorem negSucc_ofNat_add_negSucc_ofNat (m n : Nat) :
    -[m+1] + -[n+1] = -[succ (m + n) +1] := rfl

@[local simp] theorem ofNat_mul_ofNat (m n : Nat) :
    ofNat m * ofNat n = ofNat (m * n) := rfl
@[local simp] theorem ofNat_mul_negSucc_ofNat (m n : Nat) :
    ofNat m * -[n+1] = negOfNat (m * succ n) := rfl
@[local simp] theorem negSucc_ofNat_ofNat (m n : Nat) :
    -[m+1] * ofNat n = negOfNat (succ m * n) := rfl
@[local simp] theorem mul_negSucc_ofNat_negSucc_ofNat (m n : Nat) :
    -[m+1] * -[n+1] = ofNat (succ m * succ n) := rfl

/- ## some basic functions and properties -/

protected theorem coe_nat_inj {m n : Nat} : (↑m : Int) = ↑n → m = n := Int.ofNat.inj

theorem ofNat_eq_ofNat_iff (m n : Nat) : ofNat m = ofNat n ↔ m = n := ⟨ofNat.inj, congrArg _⟩

theorem negSucc_ofNat_inj_iff : negSucc m = negSucc n ↔ m = n := ⟨negSucc.inj, λ H => by simp [H]⟩

theorem negSucc_ofNat_eq (n : Nat) : -[n+1] = -(↑n + 1) := rfl

/- ## neg -/

protected theorem neg_neg : ∀ a : Int, -(-a) = a
  | 0      => rfl
  | succ _ => rfl
  | -[_+1] => rfl

protected theorem neg_inj {a b : Int} (h : -a = -b) : a = b := by
  rw [← Int.neg_neg a, ← Int.neg_neg b, h]

protected theorem sub_eq_add_neg {a b : Int} : a - b = a + -b := rfl

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

theorem subNatNat_add_left : subNatNat (m + n) m = ofNat n := by
  unfold subNatNat; rw [Nat.sub_eq_zero_of_le (Nat.le_add_right ..), Nat.add_sub_cancel_left]

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

theorem subNatNat_of_le {m n : Nat} (h : n ≤ m) : subNatNat m n = ofNat (m - n) :=
  subNatNat_of_sub_eq_zero (Nat.sub_eq_zero_of_le h)

theorem subNatNat_of_lt {m n : Nat} (h : m < n) : subNatNat m n = -[pred (n - m) +1] :=
  subNatNat_of_sub_eq_succ <| (Nat.succ_pred_eq_of_pos (Nat.sub_pos_of_lt h)).symm

/- ## natAbs -/

theorem natAbs_ofNat (n : Nat) : natAbs ↑n = n := rfl

theorem eq_zero_ofNatAbs_eq_zero : ∀ {a : Int}, natAbs a = 0 → a = 0
  | ofNat _, H => congrArg ofNat H
  | -[_+1],  H => absurd H (succ_ne_zero _)

theorem natAbs_pos_of_ne_zero (h : a ≠ 0) : 0 < natAbs a :=
  (eq_zero_or_pos _).resolve_left <| mt eq_zero_ofNatAbs_eq_zero h

theorem natAbs_zero : natAbs (0 : Int) = (0 : Nat) := rfl

theorem natAbs_one : natAbs (1 : Int) = (1 : Nat) := rfl

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

/- ## sign -/

@[simp] theorem sign_zero : sign 0 = 0 := rfl
@[simp] theorem sign_one : sign 1 = 1 := rfl
@[simp] theorem sign_neg_one : sign (-1) = -1 := rfl

/- # ring properties -/

/- addition -/

protected theorem add_comm : ∀ a b : Int, a + b = b + a
  | ofNat n, ofNat m => by simp [Nat.add_comm]
  | ofNat _, -[_+1]  => rfl
  | -[_+1],  ofNat _ => rfl
  | -[_+1],  -[_+1]  => by simp [Nat.add_comm]

protected theorem add_zero : ∀ a : Int, a + 0 = a
  | ofNat _ => rfl
  | -[_+1]  => rfl

protected theorem zero_add (a : Int) : 0 + a = a := Int.add_comm .. ▸ a.add_zero

theorem subNatNat_sub (h : n ≤ m) (k : Nat) : subNatNat (m - n) k = subNatNat m (k + n) := by
  rwa [← subNatNat_add_add _ _ n, Nat.sub_add_cancel]

theorem subNatNat_add (m n k : Nat) : subNatNat (m + n) k = ofNat m + subNatNat n k := by
  cases n.lt_or_ge k with
  | inl h' =>
    simp [subNatNat_of_lt h', succ_pred_eq_of_pos (Nat.sub_pos_of_lt h')]
    conv => lhs; rw [← Nat.sub_add_cancel (Nat.le_of_lt h')]
    apply subNatNat_add_add
  | inr h' => simp [subNatNat_of_le h',
      subNatNat_of_le (Nat.le_trans h' (le_add_left ..)), Nat.add_sub_assoc h']

theorem subNatNat_add_negSucc_ofNat (m n k : Nat) : subNatNat m n + -[k+1] = subNatNat m (n + succ k) := by
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
    rw [← add_succ, succ_pred_eq_of_pos (Nat.sub_pos_of_lt h'), add_succ, succ_sub h₃, Nat.pred_succ]
    rw [Nat.add_comm n, Nat.add_sub_assoc (Nat.le_of_lt h')]

protected theorem add_assoc : ∀ a b c : Int, a + b + c = a + (b + c)
  | ofNat m, ofNat n, c => aux1 ..
  | ofNat m, b, ofNat k => by
    rw [Int.add_comm, ← aux1, Int.add_comm k, aux1, Int.add_comm b]
  | a, ofNat n, ofNat k => by
    rw [Int.add_comm, Int.add_comm a, ← aux1, Int.add_comm a, Int.add_comm (ofNat k)]
  | -[m+1], -[n+1], ofNat k => aux2 ..
  | -[m+1], ofNat n, -[k+1] => by
    rw [Int.add_comm, ← aux2, Int.add_comm n, ← aux2, Int.add_comm -[m+1]]
  | ofNat m, -[n+1], -[k+1] => by
    rw [Int.add_comm, Int.add_comm (ofNat m), Int.add_comm m, ← aux2, Int.add_comm -[k+1]]
  | -[m+1], -[n+1], -[k+1] => by
    simp [add_succ, Nat.add_comm, Nat.add_left_comm, neg_ofNat_of_succ]
where
  aux1 (m n : Nat) : ∀ c : Int, ofNat m + ofNat n + c = ofNat m + (ofNat n + c)
    | ofNat k => by simp [Nat.add_assoc]
    | -[k+1]  => by simp [subNatNat_add]
  aux2 (m n k : Nat) : -[m+1] + -[n+1] + k = -[m+1] + (-[n+1] + k) := by
    simp [add_succ]
    rw [Int.add_comm, subNatNat_add_negSucc_ofNat]
    simp [add_succ, succ_add, Nat.add_comm]

/- ## negation -/

theorem sub_nat_self : ∀ n, subNatNat n n = 0
  | 0      => rfl
  | succ m => by rw [subNatNat_of_sub_eq_zero (Nat.sub_self ..), Nat.sub_self, ofNat_zero]

attribute [local simp] sub_nat_self

protected theorem add_left_neg : ∀ a : Int, -a + a = 0
  | 0      => rfl
  | succ m => by simp
  | -[m+1] => by simp

protected theorem add_right_neg (a : Int) : a + -a = 0 := by
  rw [Int.add_comm, Int.add_left_neg]

/- ## multiplication -/

protected theorem mul_comm (a b : Int) : a * b = b * a := by
  cases a <;> cases b <;> simp [Nat.mul_comm]

theorem ofNat_mul_negOfNat (m n : Nat) : ofNat m * negOfNat n = negOfNat (m * n) := by
  cases n <;> rfl

theorem negOfNat_mul_ofNat (m n : Nat) : negOfNat m * ofNat n = negOfNat (m * n) := by
  rw [Int.mul_comm]; simp [ofNat_mul_negOfNat, Nat.mul_comm]

theorem negSucc_ofNat_mul_negOfNat (m n : Nat) : -[m+1] * negOfNat n = ofNat (succ m * n) := by
  cases n <;> rfl

theorem negOfNat_mul_negSucc_ofNat (m n : Nat) : negOfNat n * -[m+1] = ofNat (n * succ m) := by
  rw [Int.mul_comm, negSucc_ofNat_mul_negOfNat, Nat.mul_comm]

attribute [local simp] ofNat_mul_negOfNat negOfNat_mul_ofNat
  negSucc_ofNat_mul_negOfNat negOfNat_mul_negSucc_ofNat

protected theorem mul_assoc (a b c : Int) : a * b * c = a * (b * c) := by
  cases a <;> cases b <;> cases c <;> simp [Nat.mul_assoc]

protected theorem mul_zero (a : Int) : a * 0 = 0 := by cases a <;> rfl

protected theorem zero_mul (a : Int) : 0 * a = 0 := Int.mul_comm .. ▸ a.mul_zero

theorem negOfNat_eq_subNatNat_zero (n) : negOfNat n = subNatNat 0 n := by cases n <;> rfl

theorem ofNat_mul_subNatNat (m n k : Nat) :
    ofNat m * subNatNat n k = subNatNat (m * n) (m * k) := by
  cases m with
  | zero => simp [ofNat_zero, Int.zero_mul, Nat.zero_mul]
  | succ m => cases n.lt_or_ge k with
    | inl h =>
      have h' : succ m * n < succ m * k := Nat.mul_lt_mul_of_pos_left h (Nat.succ_pos m)
      simp [subNatNat_of_lt h, subNatNat_of_lt h']
      rw [succ_pred_eq_of_pos (Nat.sub_pos_of_lt h), ← neg_ofNat_of_succ, Nat.mul_sub_left_distrib,
        ← succ_pred_eq_of_pos (Nat.sub_pos_of_lt h')]; rfl
    | inr h =>
      have h' : succ m * k ≤ succ m * n := Nat.mul_le_mul_left _ h
      simp [subNatNat_of_le h, subNatNat_of_le h', Nat.mul_sub_left_distrib]

theorem negOfNat_add (m n : Nat) : negOfNat m + negOfNat n = negOfNat (m + n) := by
  cases m <;> cases n <;> simp [Nat.succ_add] <;> rfl

theorem negSucc_ofNat_mul_subNatNat (m n k : Nat) :
    -[m+1] * subNatNat n k = subNatNat (succ m * k) (succ m * n) := by
  cases n.lt_or_ge k with
  | inl h =>
    have h' : succ m * n < succ m * k := Nat.mul_lt_mul_of_pos_left h (Nat.succ_pos m)
    rw [subNatNat_of_lt h, subNatNat_of_le (Nat.le_of_lt h')]
    simp [succ_pred_eq_of_pos (Nat.sub_pos_of_lt h), Nat.mul_sub_left_distrib]
  | inr h => cases Nat.lt_or_ge k n with
    | inl h' =>
      have h₁ : succ m * n > succ m * k := Nat.mul_lt_mul_of_pos_left h' (Nat.succ_pos m)
      rw [subNatNat_of_le h, subNatNat_of_lt h₁, negSucc_ofNat_ofNat,
        Nat.mul_sub_left_distrib, ← succ_pred_eq_of_pos (Nat.sub_pos_of_lt h₁)]; rfl
    | inr h' => rw [Nat.le_antisymm h h', sub_nat_self, sub_nat_self, Int.mul_zero]

attribute [local simp] ofNat_mul_subNatNat negOfNat_add negSucc_ofNat_mul_subNatNat

protected theorem distrib_left : ∀ a b c : Int, a * (b + c) = a * b + a * c
  | ofNat m, ofNat n, ofNat k => by simp [Nat.left_distrib]
  | ofNat m, ofNat n, -[k+1]  => by
    simp [negOfNat_eq_subNatNat_zero]; rw [← subNatNat_add]; rfl
  | ofNat m, -[n+1],  ofNat k => by
    simp [negOfNat_eq_subNatNat_zero]; rw [Int.add_comm, ← subNatNat_add]; rfl
  | ofNat m, -[n+1],  -[k+1]  => by simp; rw [← Nat.left_distrib, succ_add]; rfl
  | -[m+1],  ofNat n, ofNat k => by simp [Nat.mul_comm]; rw [← Nat.right_distrib, Nat.mul_comm]
  | -[m+1],  ofNat n, -[k+1]  => by
    simp [negOfNat_eq_subNatNat_zero]; rw [Int.add_comm, ← subNatNat_add]; rfl
  | -[m+1],  -[n+1],  ofNat k => by simp [negOfNat_eq_subNatNat_zero]; rw [← subNatNat_add]; rfl
  | -[m+1],  -[n+1],  -[k+1]  => by simp; rw [← Nat.left_distrib, succ_add]; rfl

protected theorem distrib_right (a b c : Int) : (a + b) * c = a * c + b * c := by
  simp [Int.mul_comm, Int.distrib_left]

protected theorem zero_ne_one : (0 : Int) ≠ 1 := fun.

theorem ofNat_sub (h : m ≤ n) : ofNat (n - m) = ofNat n - ofNat m := by
  match m with
  | 0 => rfl
  | succ m =>
    show ofNat (n - succ m) = subNatNat n (succ m)
    rw [subNatNat, Nat.sub_eq_zero_of_le h]

protected theorem add_left_comm (a b c : Int) : a + (b + c) = b + (a + c) := by
  rw [← Int.add_assoc, Int.add_comm a, Int.add_assoc]

protected theorem add_left_cancel {a b c : Int} (h : a + b = a + c) : b = c := by
  have h₁ : -a + (a + b) = -a + (a + c) := by rw [h]
  simp [← Int.add_assoc, Int.add_left_neg, Int.zero_add] at h₁; exact h₁

protected theorem neg_add {a b : Int} : -(a + b) = -a + -b := by
  apply Int.add_left_cancel (a := a + b)
  rw [Int.add_right_neg, Int.add_comm a, ← Int.add_assoc, Int.add_assoc b,
    Int.add_right_neg, Int.add_zero, Int.add_right_neg]

theorem negSucc_ofNat_coe' (n : Nat) : -[n+1] = -↑n - 1 := by
  rw [Int.sub_eq_add_neg, ← Int.neg_add]; rfl

protected theorem subNatNat_eq_coe {m n : Nat} : subNatNat m n = ↑m - ↑n := by
  apply subNatNat_elim m n fun m n i => i = m - n
  · intros i n
    rw [Int.ofNat_add, Int.sub_eq_add_neg, Int.add_assoc, Int.add_left_comm,
      Int.add_right_neg, Int.add_zero]
  · intros i n
    simp only [negSucc_ofNat_coe, ofNat_add, Int.sub_eq_add_neg, Int.neg_add, ← Int.add_assoc]
    rw [← @Int.sub_eq_add_neg n, ← ofNat_sub, Nat.sub_self, ofNat_zero, Int.zero_add]
    apply Nat.le_refl

theorem toNat_sub (m n : Nat) : toNat (m - n : Nat) = m - n := rfl

protected theorem one_mul : ∀ a : Int, 1 * a = a
  | ofNat n => show ofNat (1 * n) = ofNat n by rw [Nat.one_mul]
  | -[n+1]  => show -[1 * n +1] = -[n+1] by rw [Nat.one_mul]

protected theorem mul_one (a : Int) : a * 1 = a := by
  rw [Int.mul_comm, Int.one_mul]

protected theorem neg_eq_neg_one_mul : ∀ a : Int, -a = -1 * a
  | 0      => rfl
  | succ n => show _ = -[1 * n +1] by rw [Nat.one_mul] rfl
  | -[n+1] => show _ = ofNat _ by rw [Nat.one_mul] rfl

theorem sign_mul_natAbs : ∀ a : Int, sign a * natAbs a = a
  | 0      => rfl
  | succ _ => Int.one_mul _
  | -[_+1] => (Int.neg_eq_neg_one_mul _).symm

end Int

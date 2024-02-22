/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Mario Carneiro
-/
import Std.Data.Nat.Lemmas
import Std.Data.Int.Order
import Std.Data.Int.Init.DivMod

/-!
# Lemmas about integer division
-/


open Nat

namespace Int

/-! ### `/`  -/

theorem ofNat_div (m n : Nat) : ↑(m / n) = div ↑m ↑n := rfl

theorem ofNat_fdiv : ∀ m n : Nat, ↑(m / n) = fdiv ↑m ↑n
  | 0, _ => by simp [fdiv]
  | succ _, _ => rfl

theorem negSucc_ediv (m : Nat) {b : Int} (H : 0 < b) : -[m+1] / b = -(div m b + 1) :=
  match b, eq_succ_of_zero_lt H with
  | _, ⟨_, rfl⟩ => rfl

@[simp] protected theorem zero_div : ∀ b : Int, div 0 b = 0
  | ofNat _ => show ofNat _ = _ by simp
  | -[_+1] => show -ofNat _ = _ by simp

@[simp] theorem zero_fdiv (b : Int) : fdiv 0 b = 0 := by cases b <;> rfl

@[simp] protected theorem div_zero : ∀ a : Int, div a 0 = 0
  | ofNat _ => show ofNat _ = _ by simp
  | -[_+1] => rfl

@[simp] protected theorem fdiv_zero : ∀ a : Int, fdiv a 0 = 0
  | 0      => rfl
  | succ _ => rfl
  | -[_+1] => rfl

theorem fdiv_eq_ediv : ∀ (a : Int) {b : Int}, 0 ≤ b → fdiv a b = a / b
  | 0, _, _ | -[_+1], 0, _ => by simp
  | succ _, ofNat _, _ | -[_+1], succ _, _ => rfl

theorem div_eq_ediv : ∀ {a b : Int}, 0 ≤ a → 0 ≤ b → a.div b = a / b
  | 0, _, _, _ | _, 0, _, _ => by simp
  | succ _, succ _, _, _ => rfl

theorem fdiv_eq_div {a b : Int} (Ha : 0 ≤ a) (Hb : 0 ≤ b) : fdiv a b = div a b :=
  div_eq_ediv Ha Hb ▸ fdiv_eq_ediv _ Hb

@[simp] protected theorem div_neg : ∀ a b : Int, a.div (-b) = -(a.div b)
  | ofNat m, 0 => show ofNat (m / 0) = -↑(m / 0) by rw [Nat.div_zero]; rfl
  | ofNat m, -[n+1] | -[m+1], succ n => (Int.neg_neg _).symm
  | ofNat m, succ n | -[m+1], 0 | -[m+1], -[n+1] => rfl

-- Lean 4 core provides an instance for `Div Int` using `Int.div`.
-- Even though we provide a higher priority instance in `Std.Data.Int.Basic`,
-- we provide a `simp` lemma here to unfold usages of that instance back to `Int.div`.
@[simp] theorem div_def' (a b : Int) :
    @HDiv.hDiv Int Int Int (@instHDiv Int Int.instDivInt) a b = Int.div a b := rfl

@[simp] protected theorem neg_div : ∀ a b : Int, (-a).div b = -(a.div b)
  | 0, n => by simp [Int.neg_zero]
  | succ m, (n:Nat) | -[m+1], 0 | -[m+1], -[n+1] => rfl
  | succ m, -[n+1] | -[m+1], succ n => (Int.neg_neg _).symm

protected theorem neg_div_neg (a b : Int) : (-a).div (-b) = a.div b := by
  simp [Int.div_neg, Int.neg_div, Int.neg_neg]

protected theorem div_nonneg {a b : Int} (Ha : 0 ≤ a) (Hb : 0 ≤ b) : 0 ≤ a.div b :=
  match a, b, eq_ofNat_of_zero_le Ha, eq_ofNat_of_zero_le Hb with
  | _, _, ⟨_, rfl⟩, ⟨_, rfl⟩ => ofNat_zero_le _

theorem fdiv_nonneg {a b : Int} (Ha : 0 ≤ a) (Hb : 0 ≤ b) : 0 ≤ a.fdiv b :=
  match a, b, eq_ofNat_of_zero_le Ha, eq_ofNat_of_zero_le Hb with
  | _, _, ⟨_, rfl⟩, ⟨_, rfl⟩ => ofNat_fdiv .. ▸ ofNat_zero_le _

theorem ediv_nonneg {a b : Int} (Ha : 0 ≤ a) (Hb : 0 ≤ b) : 0 ≤ a / b :=
  match a, b, eq_ofNat_of_zero_le Ha, eq_ofNat_of_zero_le Hb with
  | _, _, ⟨_, rfl⟩, ⟨_, rfl⟩ => ofNat_zero_le _

protected theorem div_nonpos {a b : Int} (Ha : 0 ≤ a) (Hb : b ≤ 0) : a.div b ≤ 0 :=
  Int.nonpos_of_neg_nonneg <| Int.div_neg .. ▸ Int.div_nonneg Ha (Int.neg_nonneg_of_nonpos Hb)

theorem fdiv_nonpos : ∀ {a b : Int}, 0 ≤ a → b ≤ 0 → a.fdiv b ≤ 0
  | 0, 0, _, _ | 0, -[_+1], _, _ | succ _, 0, _, _ | succ _, -[_+1], _, _ => ⟨_⟩

theorem ediv_nonpos {a b : Int} (Ha : 0 ≤ a) (Hb : b ≤ 0) : a / b ≤ 0 :=
  Int.nonpos_of_neg_nonneg <| Int.ediv_neg .. ▸ Int.ediv_nonneg Ha (Int.neg_nonneg_of_nonpos Hb)

theorem fdiv_neg' : ∀ {a b : Int}, a < 0 → 0 < b → a.fdiv b < 0
  | -[_+1], succ _, _, _ => negSucc_lt_zero _

theorem ediv_neg' {a b : Int} (Ha : a < 0) (Hb : 0 < b) : a / b < 0 :=
  match a, b, eq_negSucc_of_lt_zero Ha, eq_succ_of_zero_lt Hb with
  | _, _, ⟨_, rfl⟩, ⟨_, rfl⟩ => negSucc_lt_zero _

@[simp] protected theorem div_one : ∀ a : Int, a.div 1 = a
  | (n:Nat) => congrArg ofNat (Nat.div_one _)
  | -[n+1] => by simp [Int.div, neg_ofNat_succ]

@[simp] theorem fdiv_one : ∀ a : Int, a.fdiv 1 = a
  | 0 => rfl
  | succ _ => congrArg Nat.cast (Nat.div_one _)
  | -[_+1] => congrArg negSucc (Nat.div_one _)

@[simp] theorem ediv_one : ∀ a : Int, a / 1 = a
  | (_:Nat) => congrArg Nat.cast (Nat.div_one _)
  | -[_+1]  => congrArg negSucc (Nat.div_one _)

theorem div_eq_zero_of_lt {a b : Int} (H1 : 0 ≤ a) (H2 : a < b) : a.div b = 0 :=
  match a, b, eq_ofNat_of_zero_le H1, eq_succ_of_zero_lt (Int.lt_of_le_of_lt H1 H2) with
  | _, _, ⟨_, rfl⟩, ⟨_, rfl⟩ => congrArg Nat.cast <| Nat.div_eq_of_lt <| ofNat_lt.1 H2

theorem ediv_eq_zero_of_lt {a b : Int} (H1 : 0 ≤ a) (H2 : a < b) : a / b = 0 :=
  match a, b, eq_ofNat_of_zero_le H1, eq_succ_of_zero_lt (Int.lt_of_le_of_lt H1 H2) with
  | _, _, ⟨_, rfl⟩, ⟨_, rfl⟩ => congrArg Nat.cast <| Nat.div_eq_of_lt <| ofNat_lt.1 H2

theorem add_mul_ediv_left (a : Int) {b : Int}
    (c : Int) (H : b ≠ 0) : (a + b * c) / b = a / b + c :=
  Int.mul_comm .. ▸ Int.add_mul_ediv_right _ _ H

@[simp] theorem mul_fdiv_cancel (a : Int) {b : Int} (H : b ≠ 0) : fdiv (a * b) b = a :=
  if b0 : 0 ≤ b then by
    rw [fdiv_eq_ediv _ b0, mul_ediv_cancel _ H]
  else
    match a, b, Int.not_le.1 b0 with
    | 0, _, _ => by simp [Int.zero_mul]
    | succ a, -[b+1], _ => congrArg ofNat <| Nat.mul_div_cancel (succ a) b.succ_pos
    | -[a+1], -[b+1], _ => congrArg negSucc <| Nat.div_eq_of_lt_le
      (le_of_lt_succ <| Nat.mul_lt_mul_of_pos_right a.lt_succ_self b.succ_pos)
      (lt_succ_self _)

@[simp] protected theorem mul_div_cancel (a : Int) {b : Int} (H : b ≠ 0) : (a * b).div b = a :=
  have : ∀ {a b : Nat}, (b : Int) ≠ 0 → (div (a * b) b : Int) = a := fun H => by
    rw [← ofNat_mul, ← ofNat_div,
      Nat.mul_div_cancel _ <| Nat.pos_of_ne_zero <| Int.ofNat_ne_zero.1 H]
  match a, b, a.eq_nat_or_neg, b.eq_nat_or_neg with
  | _, _, ⟨a, .inl rfl⟩, ⟨b, .inl rfl⟩ => this H
  | _, _, ⟨a, .inl rfl⟩, ⟨b, .inr rfl⟩ => by
    rw [Int.mul_neg, Int.neg_div, Int.div_neg, Int.neg_neg,
      this (Int.neg_ne_zero.1 H)]
  | _, _, ⟨a, .inr rfl⟩, ⟨b, .inl rfl⟩ => by rw [Int.neg_mul, Int.neg_div, this H]
  | _, _, ⟨a, .inr rfl⟩, ⟨b, .inr rfl⟩ => by
    rw [Int.neg_mul_neg, Int.div_neg, this (Int.neg_ne_zero.1 H)]

@[simp] protected theorem mul_div_cancel_left (b : Int) (H : a ≠ 0) : (a * b).div a = b :=
  Int.mul_comm .. ▸ Int.mul_div_cancel _ H

@[simp] theorem mul_fdiv_cancel_left (b : Int) (H : a ≠ 0) : fdiv (a * b) a = b :=
  Int.mul_comm .. ▸ Int.mul_fdiv_cancel _ H

@[simp] protected theorem div_self {a : Int} (H : a ≠ 0) : a.div a = 1 := by
  have := Int.mul_div_cancel 1 H; rwa [Int.one_mul] at this

@[simp] protected theorem fdiv_self {a : Int} (H : a ≠ 0) : a.fdiv a = 1 := by
  have := Int.mul_fdiv_cancel 1 H; rwa [Int.one_mul] at this

@[simp] protected theorem ediv_self {a : Int} (H : a ≠ 0) : a / a = 1 := by
  have := Int.mul_ediv_cancel 1 H; rwa [Int.one_mul] at this

/-! ### mod -/

theorem ofNat_fmod (m n : Nat) : ↑(m % n) = fmod m n := by cases m <;> simp [fmod]

theorem negSucc_emod (m : Nat) {b : Int} (bpos : 0 < b) : -[m+1] % b = b - 1 - m % b := by
  rw [Int.sub_sub, Int.add_comm]
  match b, eq_succ_of_zero_lt bpos with
  | _, ⟨n, rfl⟩ => rfl

@[simp] theorem zero_mod (b : Int) : mod 0 b = 0 := by cases b <;> simp [mod]

@[simp] theorem zero_fmod (b : Int) : fmod 0 b = 0 := by cases b <;> rfl

@[simp] theorem mod_zero : ∀ a : Int, mod a 0 = a
  | ofNat _ => congrArg ofNat <| Nat.mod_zero _
  | -[_+1] => rfl

@[simp] theorem fmod_zero : ∀ a : Int, fmod a 0 = a
  | 0 => rfl
  | succ _ => congrArg ofNat <| Nat.mod_zero _
  | -[_+1]  => congrArg negSucc <| Nat.mod_zero _

theorem mod_add_div : ∀ a b : Int, mod a b + b * (a.div b) = a
  | ofNat _, ofNat _ => congrArg ofNat (Nat.mod_add_div ..)
  | ofNat m, -[n+1] => by
    show (m % succ n + -↑(succ n) * -↑(m / succ n) : Int) = m
    rw [Int.neg_mul_neg]; exact congrArg ofNat (Nat.mod_add_div ..)
  | -[_+1], 0 => rfl
  | -[m+1], ofNat n => by
    show -(↑((succ m) % n) : Int) + ↑n * -↑(succ m / n) = -↑(succ m)
    rw [Int.mul_neg, ← Int.neg_add]
    exact congrArg (-ofNat ·) (Nat.mod_add_div ..)
  | -[m+1], -[n+1] => by
    show -(↑(succ m % succ n) : Int) + -↑(succ n) * ↑(succ m / succ n) = -↑(succ m)
    rw [Int.neg_mul, ← Int.neg_add]
    exact congrArg (-ofNat ·) (Nat.mod_add_div ..)

theorem fmod_add_fdiv : ∀ a b : Int, a.fmod b + b * a.fdiv b = a
  | 0, ofNat _ | 0, -[_+1] => congrArg ofNat <| by simp
  | succ m, ofNat n => congrArg ofNat <| Nat.mod_add_div ..
  | succ m, -[n+1] => by
    show subNatNat (m % succ n) n + (↑(succ n * (m / succ n)) + n + 1) = (m + 1)
    rw [Int.add_comm _ n, ← Int.add_assoc, ← Int.add_assoc,
      Int.subNatNat_eq_coe, Int.sub_add_cancel]
    exact congrArg (ofNat · + 1) <| Nat.mod_add_div ..
  | -[_+1], 0 => by rw [fmod_zero]; rfl
  | -[m+1], succ n => by
    show subNatNat .. - (↑(succ n * (m / succ n)) + ↑(succ n)) = -↑(succ m)
    rw [Int.subNatNat_eq_coe, ← Int.sub_sub, ← Int.neg_sub, Int.sub_sub, Int.sub_sub_self]
    exact congrArg (-ofNat ·) <| Nat.succ_add .. ▸ Nat.mod_add_div .. ▸ rfl
  | -[m+1], -[n+1] => by
    show -(↑(succ m % succ n) : Int) + -↑(succ n * (succ m / succ n)) = -↑(succ m)
    rw [← Int.neg_add]; exact congrArg (-ofNat ·) <| Nat.mod_add_div ..

theorem div_add_mod (a b : Int) : b * a.div b + mod a b = a :=
  (Int.add_comm ..).trans (mod_add_div ..)

theorem fdiv_add_fmod (a b : Int) : b * a.fdiv b + a.fmod b = a :=
  (Int.add_comm ..).trans (fmod_add_fdiv ..)

theorem mod_def (a b : Int) : mod a b = a - b * a.div b := by
  rw [← Int.add_sub_cancel (mod a b), mod_add_div]

theorem fmod_def (a b : Int) : a.fmod b = a - b * a.fdiv b := by
  rw [← Int.add_sub_cancel (a.fmod b), fmod_add_fdiv]

theorem fmod_eq_emod (a : Int) {b : Int} (hb : 0 ≤ b) : fmod a b = a % b := by
  simp [fmod_def, emod_def, fdiv_eq_ediv _ hb]

theorem mod_eq_emod {a b : Int} (ha : 0 ≤ a) (hb : 0 ≤ b) : mod a b = a % b := by
  simp [emod_def, mod_def, div_eq_ediv ha hb]

theorem fmod_eq_mod {a b : Int} (Ha : 0 ≤ a) (Hb : 0 ≤ b) : fmod a b = mod a b :=
  mod_eq_emod Ha Hb ▸ fmod_eq_emod _ Hb

@[simp] theorem mod_neg (a b : Int) : mod a (-b) = mod a b := by
  rw [mod_def, mod_def, Int.div_neg, Int.neg_mul_neg]

@[simp] theorem emod_neg (a b : Int) : a % -b = a % b := by
  rw [emod_def, emod_def, Int.ediv_neg, Int.neg_mul_neg]

@[simp] theorem mod_one (a : Int) : mod a 1 = 0 := by
  simp [mod_def, Int.div_one, Int.one_mul, Int.sub_self]

@[local simp] theorem emod_one (a : Int) : a % 1 = 0 := by
  simp [emod_def, Int.one_mul, Int.sub_self]

@[simp] theorem fmod_one (a : Int) : a.fmod 1 = 0 := by
  simp [fmod_def, Int.one_mul, Int.sub_self]

theorem emod_eq_of_lt {a b : Int} (H1 : 0 ≤ a) (H2 : a < b) : a % b = a :=
  have b0 := Int.le_trans H1 (Int.le_of_lt H2)
  match a, b, eq_ofNat_of_zero_le H1, eq_ofNat_of_zero_le b0 with
  | _, _, ⟨_, rfl⟩, ⟨_, rfl⟩ => congrArg ofNat <| Nat.mod_eq_of_lt (Int.ofNat_lt.1 H2)

@[simp] theorem emod_self_add_one {x : Int} (h : 0 ≤ x) : x % (x + 1) = x :=
  emod_eq_of_lt h (Int.lt_succ x)

theorem mod_eq_of_lt {a b : Int} (H1 : 0 ≤ a) (H2 : a < b) : mod a b = a := by
  rw [mod_eq_emod H1 (Int.le_trans H1 (Int.le_of_lt H2)), emod_eq_of_lt H1 H2]

theorem fmod_eq_of_lt {a b : Int} (H1 : 0 ≤ a) (H2 : a < b) : a.fmod b = a := by
  rw [fmod_eq_emod _ (Int.le_trans H1 (Int.le_of_lt H2)), emod_eq_of_lt H1 H2]

theorem mod_nonneg : ∀ {a : Int} (b : Int), 0 ≤ a → 0 ≤ mod a b
  | ofNat _, -[_+1], _ | ofNat _, ofNat _, _ => ofNat_nonneg _

theorem fmod_nonneg {a b : Int} (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a.fmod b :=
  fmod_eq_mod ha hb ▸ mod_nonneg _ ha

theorem fmod_nonneg' (a : Int) {b : Int} (hb : 0 < b) : 0 ≤ a.fmod b :=
  fmod_eq_emod _ (Int.le_of_lt hb) ▸ emod_nonneg _ (Int.ne_of_lt hb).symm

theorem mod_lt_of_pos (a : Int) {b : Int} (H : 0 < b) : mod a b < b :=
  match a, b, eq_succ_of_zero_lt H with
  | ofNat _, _, ⟨n, rfl⟩ => ofNat_lt.2 <| Nat.mod_lt _ n.succ_pos
  | -[_+1], _, ⟨n, rfl⟩ => Int.lt_of_le_of_lt
    (Int.neg_nonpos_of_nonneg <| Int.ofNat_nonneg _) (ofNat_pos.2 n.succ_pos)

theorem fmod_lt_of_pos (a : Int) {b : Int} (H : 0 < b) : a.fmod b < b :=
  fmod_eq_emod _ (Int.le_of_lt H) ▸ emod_lt_of_pos a H

theorem emod_two_eq (x : Int) : x % 2 = 0 ∨ x % 2 = 1 := by
  have h₁ : 0 ≤ x % 2 := Int.emod_nonneg x (by decide)
  have h₂ : x % 2 < 2 := Int.emod_lt_of_pos x (by decide)
  match x % 2, h₁, h₂ with
  | 0, _, _ => simp
  | 1, _, _ => simp

theorem mod_add_div' (m k : Int) : mod m k + m.div k * k = m := by
  rw [Int.mul_comm]; apply mod_add_div

theorem div_add_mod' (m k : Int) : m.div k * k + mod m k = m := by
  rw [Int.mul_comm]; apply div_add_mod

theorem ediv_add_emod' (m k : Int) : m / k * k + m % k = m := by
  rw [Int.mul_comm]; apply ediv_add_emod

theorem add_emod_eq_add_emod_left {m n k : Int} (i : Int)
    (H : m % n = k % n) : (i + m) % n = (i + k) % n := by
  rw [Int.add_comm, add_emod_eq_add_emod_right _ H, Int.add_comm]

theorem emod_add_cancel_left {m n k i : Int} : (i + m) % n = (i + k) % n ↔ m % n = k % n := by
  rw [Int.add_comm, Int.add_comm i, emod_add_cancel_right]

theorem emod_sub_cancel_right {m n k : Int} (i) : (m - i) % n = (k - i) % n ↔ m % n = k % n :=
  emod_add_cancel_right _

theorem emod_eq_emod_iff_emod_sub_eq_zero {m n k : Int} : m % n = k % n ↔ (m - k) % n = 0 :=
  (emod_sub_cancel_right k).symm.trans <| by simp [Int.sub_self]

@[simp] theorem mul_mod_left (a b : Int) : (a * b).mod b = 0 :=
  if h : b = 0 then by simp [h, Int.mul_zero] else by
    rw [Int.mod_def, Int.mul_div_cancel _ h, Int.mul_comm, Int.sub_self]

@[simp] theorem mul_fmod_left (a b : Int) : (a * b).fmod b = 0 :=
  if h : b = 0 then by simp [h, Int.mul_zero] else by
    rw [Int.fmod_def, Int.mul_fdiv_cancel _ h, Int.mul_comm, Int.sub_self]

@[simp] theorem mul_mod_right (a b : Int) : (a * b).mod a = 0 := by
  rw [Int.mul_comm, mul_mod_left]

@[simp] theorem mul_fmod_right (a b : Int) : (a * b).fmod a = 0 := by
  rw [Int.mul_comm, mul_fmod_left]

@[simp] theorem mod_self {a : Int} : a.mod a = 0 := by
  have := mul_mod_left 1 a; rwa [Int.one_mul] at this

@[simp] theorem fmod_self {a : Int} : a.fmod a = 0 := by
  have := mul_fmod_left 1 a; rwa [Int.one_mul] at this

protected theorem ediv_emod_unique {a b r q : Int} (h : 0 < b) :
  a / b = q ∧ a % b = r ↔ r + b * q = a ∧ 0 ≤ r ∧ r < b := by
  constructor
  · intro ⟨rfl, rfl⟩
    exact ⟨emod_add_ediv a b, emod_nonneg _ (Int.ne_of_gt h), emod_lt_of_pos _ h⟩
  · intro ⟨rfl, hz, hb⟩
    constructor
    · rw [Int.add_mul_ediv_left r q (Int.ne_of_gt h), ediv_eq_zero_of_lt hz hb]
      simp [Int.zero_add]
    · rw [add_mul_emod_self_left, emod_eq_of_lt hz hb]

/-! ### properties of `/` and `%` -/

@[simp] theorem mul_ediv_mul_of_pos {a : Int}
    (b c : Int) (H : 0 < a) : (a * b) / (a * c) = b / c :=
  suffices ∀ (m k : Nat) (b : Int), (m.succ * b) / (m.succ * k) = b / k from
    match a, eq_succ_of_zero_lt H, c, Int.eq_nat_or_neg c with
    | _, ⟨m, rfl⟩, _, ⟨k, .inl rfl⟩ => this _ ..
    | _, ⟨m, rfl⟩, _, ⟨k, .inr rfl⟩ => by
      rw [Int.mul_neg, Int.ediv_neg, Int.ediv_neg]; apply congrArg Neg.neg; apply this
  fun m k b =>
  match b, k with
  | ofNat n, k => congrArg ofNat (Nat.mul_div_mul_left _ _ m.succ_pos)
  | -[n+1], 0 => by
    rw [Int.ofNat_zero, Int.mul_zero, Int.ediv_zero, Int.ediv_zero]
  | -[n+1], succ k => congrArg negSucc <|
    show (m.succ * n + m) / (m.succ * k.succ) = n / k.succ by
      apply Nat.div_eq_of_lt_le
      · refine Nat.le_trans ?_ (Nat.le_add_right _ _)
        rw [← Nat.mul_div_mul_left _ _ m.succ_pos]
        apply Nat.div_mul_le_self
      · show m.succ * n.succ ≤ _
        rw [Nat.mul_left_comm]
        apply Nat.mul_le_mul_left
        apply (Nat.div_lt_iff_lt_mul k.succ_pos).1
        apply Nat.lt_succ_self


@[simp] theorem mul_ediv_mul_of_pos_left
    (a : Int) {b : Int} (c : Int) (H : 0 < b) : (a * b) / (c * b) = a / c := by
  rw [Int.mul_comm, Int.mul_comm c, mul_ediv_mul_of_pos _ _ H]

@[simp] theorem mul_emod_mul_of_pos
    {a : Int} (b c : Int) (H : 0 < a) : (a * b) % (a * c) = a * (b % c) := by
  rw [emod_def, emod_def, mul_ediv_mul_of_pos _ _ H, Int.mul_sub, Int.mul_assoc]

theorem lt_div_add_one_mul_self (a : Int) {b : Int} (H : 0 < b) : a < (a.div b + 1) * b := by
  rw [Int.add_mul, Int.one_mul, Int.mul_comm]
  exact Int.lt_add_of_sub_left_lt <| Int.mod_def .. ▸ mod_lt_of_pos _ H

theorem lt_ediv_add_one_mul_self (a : Int) {b : Int} (H : 0 < b) : a < (a / b + 1) * b := by
  rw [Int.add_mul, Int.one_mul, Int.mul_comm]
  exact Int.lt_add_of_sub_left_lt <| Int.emod_def .. ▸ emod_lt_of_pos _ H

theorem lt_fdiv_add_one_mul_self (a : Int) {b : Int} (H : 0 < b) : a < (a.fdiv b + 1) * b :=
  Int.fdiv_eq_ediv _ (Int.le_of_lt H) ▸ lt_ediv_add_one_mul_self a H

@[simp] theorem natAbs_div (a b : Int) : natAbs (a.div b) = (natAbs a).div (natAbs b) :=
  match a, b, eq_nat_or_neg a, eq_nat_or_neg b with
  | _, _, ⟨_, .inl rfl⟩, ⟨_, .inl rfl⟩ => rfl
  | _, _, ⟨_, .inl rfl⟩, ⟨_, .inr rfl⟩ => by rw [Int.div_neg, natAbs_neg, natAbs_neg]; rfl
  | _, _, ⟨_, .inr rfl⟩, ⟨_, .inl rfl⟩ => by rw [Int.neg_div, natAbs_neg, natAbs_neg]; rfl
  | _, _, ⟨_, .inr rfl⟩, ⟨_, .inr rfl⟩ => by rw [Int.neg_div_neg, natAbs_neg, natAbs_neg]; rfl

theorem natAbs_div_le_natAbs (a b : Int) : natAbs (a / b) ≤ natAbs a :=
  match b, eq_nat_or_neg b with
  | _, ⟨n, .inl rfl⟩ => aux _ _
  | _, ⟨n, .inr rfl⟩ => by rw [Int.ediv_neg, natAbs_neg]; apply aux
where
  aux : ∀ (a : Int) (n : Nat), natAbs (a / n) ≤ natAbs a
  | ofNat _, _ => Nat.div_le_self ..
  | -[_+1], 0 => Nat.zero_le _
  | -[_+1], succ _ => Nat.succ_le_succ (Nat.div_le_self _ _)

theorem ediv_le_self {a : Int} (b : Int) (Ha : 0 ≤ a) : a / b ≤ a := by
  have := Int.le_trans le_natAbs (ofNat_le.2 <| natAbs_div_le_natAbs a b)
  rwa [natAbs_of_nonneg Ha] at this

theorem mul_div_cancel_of_mod_eq_zero {a b : Int} (H : a.mod b = 0) : b * (a.div b) = a := by
  have := mod_add_div a b; rwa [H, Int.zero_add] at this

theorem div_mul_cancel_of_mod_eq_zero {a b : Int} (H : a.mod b = 0) : a.div b * b = a := by
  rw [Int.mul_comm, mul_div_cancel_of_mod_eq_zero H]

/-! ### dvd -/

protected theorem dvd_add_left {a b c : Int} (H : a ∣ c) : a ∣ b + c ↔ a ∣ b :=
  ⟨fun h => by have := Int.dvd_sub h H; rwa [Int.add_sub_cancel] at this, (Int.dvd_add · H)⟩

protected theorem dvd_add_right {a b c : Int} (H : a ∣ b) : a ∣ b + c ↔ a ∣ c := by
  rw [Int.add_comm, Int.dvd_add_left H]

protected theorem dvd_iff_dvd_of_dvd_sub {a b c : Int} (H : a ∣ b - c) : a ∣ b ↔ a ∣ c :=
  ⟨fun h => Int.sub_sub_self b c ▸ Int.dvd_sub h H,
   fun h => Int.sub_add_cancel b c ▸ Int.dvd_add H h⟩

protected theorem dvd_iff_dvd_of_dvd_add {a b c : Int} (H : a ∣ b + c) : a ∣ b ↔ a ∣ c := by
  rw [← Int.sub_neg] at H; rw [Int.dvd_iff_dvd_of_dvd_sub H, Int.dvd_neg]

theorem natAbs_dvd {a b : Int} : (a.natAbs : Int) ∣ b ↔ a ∣ b :=
  match natAbs_eq a with
  | .inl e => by rw [← e]
  | .inr e => by rw [← Int.neg_dvd, ← e]

theorem dvd_natAbs {a b : Int} : a ∣ b.natAbs ↔ a ∣ b :=
  match natAbs_eq b with
  | .inl e => by rw [← e]
  | .inr e => by rw [← Int.dvd_neg, ← e]

theorem natAbs_dvd_self {a : Int} : (a.natAbs : Int) ∣ a := by
  rw [Int.natAbs_dvd]
  exact Int.dvd_refl a

theorem dvd_natAbs_self {a : Int} : a ∣ (a.natAbs : Int) := by
  rw [Int.dvd_natAbs]
  exact Int.dvd_refl a

theorem ofNat_dvd_right {n : Nat} {z : Int} : z ∣ (↑n : Int) ↔ z.natAbs ∣ n := by
  rw [← natAbs_dvd_natAbs, natAbs_ofNat]

theorem dvd_antisymm {a b : Int} (H1 : 0 ≤ a) (H2 : 0 ≤ b) : a ∣ b → b ∣ a → a = b := by
  rw [← natAbs_of_nonneg H1, ← natAbs_of_nonneg H2]
  rw [ofNat_dvd, ofNat_dvd, ofNat_inj]
  apply Nat.dvd_antisymm

theorem dvd_of_mod_eq_zero {a b : Int} (H : mod b a = 0) : a ∣ b :=
  ⟨b.div a, (mul_div_cancel_of_mod_eq_zero H).symm⟩

theorem mod_eq_zero_of_dvd : ∀ {a b : Int}, a ∣ b → mod b a = 0
  | _, _, ⟨_, rfl⟩ => mul_mod_right ..

theorem dvd_iff_mod_eq_zero (a b : Int) : a ∣ b ↔ mod b a = 0 :=
  ⟨mod_eq_zero_of_dvd, dvd_of_mod_eq_zero⟩

/-- If `a % b = c` then `b` divides `a - c`. -/
theorem dvd_sub_of_emod_eq {a b c : Int} (h : a % b = c) : b ∣ a - c := by
  have hx : (a % b) % b = c % b := by
    rw [h]
  rw [Int.emod_emod, ← emod_sub_cancel_right c, Int.sub_self, zero_emod] at hx
  exact dvd_of_emod_eq_zero hx

protected theorem div_mul_cancel {a b : Int} (H : b ∣ a) : a.div b * b = a :=
  div_mul_cancel_of_mod_eq_zero (mod_eq_zero_of_dvd H)

protected theorem mul_div_cancel' {a b : Int} (H : a ∣ b) : a * b.div a = b := by
  rw [Int.mul_comm, Int.div_mul_cancel H]

protected theorem mul_div_assoc (a : Int) : ∀ {b c : Int}, c ∣ b → (a * b).div c = a * (b.div c)
  | _, c, ⟨d, rfl⟩ =>
    if cz : c = 0 then by simp [cz, Int.mul_zero] else by
      rw [Int.mul_left_comm, Int.mul_div_cancel_left _ cz, Int.mul_div_cancel_left _ cz]

protected theorem mul_div_assoc' (b : Int) {a c : Int} (h : c ∣ a) :
    (a * b).div c = a.div c * b := by
  rw [Int.mul_comm, Int.mul_div_assoc _ h, Int.mul_comm]

theorem div_dvd_div : ∀ {a b c : Int}, a ∣ b → b ∣ c → b.div a ∣ c.div a
  | a, _, _, ⟨b, rfl⟩, ⟨c, rfl⟩ => by
    if az : a = 0 then simp [az] else
      rw [Int.mul_div_cancel_left _ az, Int.mul_assoc, Int.mul_div_cancel_left _ az]
      apply Int.dvd_mul_right

protected theorem eq_mul_of_div_eq_right {a b c : Int}
    (H1 : b ∣ a) (H2 : a.div b = c) : a = b * c := by rw [← H2, Int.mul_div_cancel' H1]

protected theorem eq_mul_of_ediv_eq_right {a b c : Int}
    (H1 : b ∣ a) (H2 : a / b = c) : a = b * c := by rw [← H2, Int.mul_ediv_cancel' H1]

protected theorem div_eq_of_eq_mul_right {a b c : Int}
    (H1 : b ≠ 0) (H2 : a = b * c) : a.div b = c := by rw [H2, Int.mul_div_cancel_left _ H1]

protected theorem ediv_eq_of_eq_mul_right {a b c : Int}
    (H1 : b ≠ 0) (H2 : a = b * c) : a / b = c := by rw [H2, Int.mul_ediv_cancel_left _ H1]

protected theorem eq_div_of_mul_eq_right {a b c : Int}
    (H1 : a ≠ 0) (H2 : a * b = c) : b = c.div a :=
  (Int.div_eq_of_eq_mul_right H1 H2.symm).symm

protected theorem eq_ediv_of_mul_eq_right {a b c : Int}
    (H1 : a ≠ 0) (H2 : a * b = c) : b = c / a :=
  (Int.ediv_eq_of_eq_mul_right H1 H2.symm).symm

protected theorem div_eq_iff_eq_mul_right {a b c : Int}
    (H : b ≠ 0) (H' : b ∣ a) : a.div b = c ↔ a = b * c :=
  ⟨Int.eq_mul_of_div_eq_right H', Int.div_eq_of_eq_mul_right H⟩

protected theorem ediv_eq_iff_eq_mul_right {a b c : Int}
    (H : b ≠ 0) (H' : b ∣ a) : a / b = c ↔ a = b * c :=
  ⟨Int.eq_mul_of_ediv_eq_right H', Int.ediv_eq_of_eq_mul_right H⟩

protected theorem div_eq_iff_eq_mul_left {a b c : Int}
    (H : b ≠ 0) (H' : b ∣ a) : a.div b = c ↔ a = c * b := by
  rw [Int.mul_comm]; exact Int.div_eq_iff_eq_mul_right H H'

protected theorem ediv_eq_iff_eq_mul_left {a b c : Int}
    (H : b ≠ 0) (H' : b ∣ a) : a / b = c ↔ a = c * b := by
  rw [Int.mul_comm]; exact Int.ediv_eq_iff_eq_mul_right H H'

protected theorem eq_mul_of_div_eq_left {a b c : Int}
    (H1 : b ∣ a) (H2 : a.div b = c) : a = c * b := by
  rw [Int.mul_comm, Int.eq_mul_of_div_eq_right H1 H2]

protected theorem eq_mul_of_ediv_eq_left {a b c : Int}
    (H1 : b ∣ a) (H2 : a / b = c) : a = c * b := by
  rw [Int.mul_comm, Int.eq_mul_of_ediv_eq_right H1 H2]

protected theorem div_eq_of_eq_mul_left {a b c : Int}
    (H1 : b ≠ 0) (H2 : a = c * b) : a.div b = c :=
  Int.div_eq_of_eq_mul_right H1 (by rw [Int.mul_comm, H2])

protected theorem ediv_eq_of_eq_mul_left {a b c : Int}
    (H1 : b ≠ 0) (H2 : a = c * b) : a / b = c :=
  Int.ediv_eq_of_eq_mul_right H1 (by rw [Int.mul_comm, H2])

protected theorem eq_zero_of_div_eq_zero {d n : Int} (h : d ∣ n) (H : n.div d = 0) : n = 0 := by
  rw [← Int.mul_div_cancel' h, H, Int.mul_zero]

protected theorem eq_zero_of_ediv_eq_zero {d n : Int} (h : d ∣ n) (H : n / d = 0) : n = 0 := by
  rw [← Int.mul_ediv_cancel' h, H, Int.mul_zero]

theorem div_eq_ediv_of_dvd {a b : Int} (h : b ∣ a) : a.div b = a / b := by
  if b0 : b = 0 then simp [b0]
  else rw [Int.div_eq_iff_eq_mul_left b0 h, ← Int.ediv_eq_iff_eq_mul_left b0 h]

theorem fdiv_eq_ediv_of_dvd : ∀ {a b : Int}, b ∣ a → a.fdiv b = a / b
  | _, b, ⟨c, rfl⟩ => by if bz : b = 0 then simp [bz] else
    rw [mul_fdiv_cancel_left _ bz, mul_ediv_cancel_left _ bz]

theorem sub_ediv_of_dvd_sub {a b c : Int}
    (hcab : c ∣ a - b) : (a - b) / c = a / c - b / c := by
  rw [← Int.add_sub_cancel ((a-b) / c), ← Int.add_ediv_of_dvd_left hcab, Int.sub_add_cancel]

@[simp] protected theorem div_left_inj {a b d : Int}
    (hda : d ∣ a) (hdb : d ∣ b) : a.div d = b.div d ↔ a = b := by
  refine ⟨fun h => ?_, congrArg (div · d)⟩
  rw [← Int.mul_div_cancel' hda, ← Int.mul_div_cancel' hdb, h]

@[simp] protected theorem ediv_left_inj {a b d : Int}
    (hda : d ∣ a) (hdb : d ∣ b) : a / d = b / d ↔ a = b := by
  refine ⟨fun h => ?_, congrArg (ediv · d)⟩
  rw [← Int.mul_ediv_cancel' hda, ← Int.mul_ediv_cancel' hdb, h]

theorem div_sign : ∀ a b, a.div (sign b) = a * sign b
  | _, succ _ => by simp [sign, Int.mul_one]
  | _, 0 => by simp [sign, Int.mul_zero]
  | _, -[_+1] => by simp [sign, Int.mul_neg, Int.mul_one]

theorem ediv_sign : ∀ a b, a / sign b = a * sign b
  | _, succ _ => by simp [sign, Int.mul_one]
  | _, 0 => by simp [sign, Int.mul_zero]
  | _, -[_+1] => by simp [sign, Int.mul_neg, Int.mul_one]

protected theorem sign_eq_div_abs (a : Int) : sign a = a.div (natAbs a) :=
  if az : a = 0 then by simp [az] else
    (Int.div_eq_of_eq_mul_left (ofNat_ne_zero.2 <| natAbs_ne_zero.2 az)
      (sign_mul_natAbs _).symm).symm

theorem mul_sign : ∀ i : Int, i * sign i = natAbs i
  | succ _ => Int.mul_one _
  | 0 => Int.mul_zero _
  | -[_+1] => Int.mul_neg_one _

theorem le_of_dvd {a b : Int} (bpos : 0 < b) (H : a ∣ b) : a ≤ b :=
  match a, b, eq_succ_of_zero_lt bpos, H with
  | ofNat _, _, ⟨n, rfl⟩, H => ofNat_le.2 <| Nat.le_of_dvd n.succ_pos <| ofNat_dvd.1 H
  | -[_+1], _, ⟨_, rfl⟩, _ => Int.le_trans (Int.le_of_lt <| negSucc_lt_zero _) (ofNat_zero_le _)

theorem eq_one_of_dvd_one {a : Int} (H : 0 ≤ a) (H' : a ∣ 1) : a = 1 :=
  match a, eq_ofNat_of_zero_le H, H' with
  | _, ⟨_, rfl⟩, H' => congrArg ofNat <| Nat.eq_one_of_dvd_one <| ofNat_dvd.1 H'

theorem eq_one_of_mul_eq_one_right {a b : Int} (H : 0 ≤ a) (H' : a * b = 1) : a = 1 :=
  eq_one_of_dvd_one H ⟨b, H'.symm⟩

theorem eq_one_of_mul_eq_one_left {a b : Int} (H : 0 ≤ b) (H' : a * b = 1) : b = 1 :=
  eq_one_of_mul_eq_one_right H <| by rw [Int.mul_comm, H']

theorem le_of_mul_le_mul_left {a b c : Int} (w : a * b ≤ a * c) (h : 0 < a) : b ≤ c := by
  have w := Int.sub_nonneg_of_le w
  rw [← Int.mul_sub] at w
  have w := Int.ediv_nonneg w (Int.le_of_lt h)
  rw [Int.mul_ediv_cancel_left _ (Int.ne_of_gt h)] at w
  exact Int.le_of_sub_nonneg w

theorem le_of_mul_le_mul_right {a b c : Int} (w : b * a ≤ c * a) (h : 0 < a) : b ≤ c := by
  rw [Int.mul_comm b, Int.mul_comm c] at w
  exact le_of_mul_le_mul_left w h

theorem lt_of_mul_lt_mul_left {a b c : Int} (w : a * b < a * c) (h : 0 ≤ a) : b < c := by
  rcases Int.lt_trichotomy b c with lt | rfl | gt
  · exact lt
  · exact False.elim (Int.lt_irrefl _ w)
  · rcases Int.lt_trichotomy a 0 with a_lt | rfl | a_gt
    · exact False.elim (Int.lt_irrefl _ (Int.lt_of_lt_of_le a_lt h))
    · exact False.elim (Int.lt_irrefl b (by simp at w))
    · have := le_of_mul_le_mul_left (Int.le_of_lt w) a_gt
      exact False.elim (Int.lt_irrefl _ (Int.lt_of_lt_of_le gt this))

theorem lt_of_mul_lt_mul_right {a b c : Int} (w : b * a < c * a) (h : 0 ≤ a) : b < c := by
  rw [Int.mul_comm b, Int.mul_comm c] at w
  exact lt_of_mul_lt_mul_left w h

/-!
# `bmod` ("balanced" mod)

-/

@[simp] theorem emod_bmod {x : Int} {m : Nat} : bmod (x % m) m = bmod x m := by
  simp [bmod]

@[simp] theorem bmod_bmod : bmod (bmod x m) m = bmod x m := by
  rw [bmod, bmod_emod]
  rfl

@[simp] theorem bmod_zero : Int.bmod 0 m = 0 := by
  dsimp [bmod]
  simp only [zero_emod, Int.zero_sub, ite_eq_left_iff, Int.neg_eq_zero]
  intro h
  rw [@Int.not_lt] at h
  match m with
  | 0 => rfl
  | (m+1) =>
    exfalso
    rw [natCast_add, ofNat_one, Int.add_assoc, add_ediv_of_dvd_right] at h
    change _ + 2 / 2 ≤ 0 at h
    rw [Int.ediv_self, ← ofNat_two, ← ofNat_ediv, add_one_le_iff, ← @Int.not_le] at h
    exact h (ofNat_nonneg _)
    all_goals decide

theorem dvd_bmod_sub_self {x : Int} {m : Nat} : (m : Int) ∣ bmod x m - x := by
  dsimp [bmod]
  split
  · exact dvd_emod_sub_self
  · rw [Int.sub_sub, Int.add_comm, ← Int.sub_sub]
    exact Int.dvd_sub dvd_emod_sub_self (Int.dvd_refl _)

theorem le_bmod {x : Int} {m : Nat} (h : 0 < m) : - (m/2) ≤ Int.bmod x m := by
  dsimp [bmod]
  have v : (m : Int) % 2 = 0 ∨ (m : Int) % 2 = 1 := emod_two_eq _
  split <;> rename_i w
  · refine Int.le_trans ?_ (Int.emod_nonneg _ ?_)
    · exact Int.neg_nonpos_of_nonneg (Int.ediv_nonneg (Int.ofNat_nonneg _) (by decide))
    · exact Int.ne_of_gt (ofNat_pos.mpr h)
  · simp [Int.not_lt] at w
    refine Int.le_trans ?_ (Int.sub_le_sub_right w _)
    rw [← ediv_add_emod m 2]
    generalize (m : Int) / 2 = q
    generalize h : (m : Int) % 2 = r at *
    rcases v with rfl | rfl
    · rw [Int.add_zero, Int.mul_ediv_cancel_left, Int.add_ediv_of_dvd_left,
        Int.mul_ediv_cancel_left, show (1 / 2 : Int) = 0 by decide, Int.add_zero,
        Int.neg_eq_neg_one_mul]
      conv => rhs; congr; rw [← Int.one_mul q]
      rw [← Int.sub_mul, show (1 - 2 : Int) = -1 by decide]
      apply Int.le_refl
      all_goals try decide
      all_goals apply Int.dvd_mul_right
    · rw [Int.add_ediv_of_dvd_left, Int.mul_ediv_cancel_left,
        show (1 / 2 : Int) = 0 by decide, Int.add_assoc, Int.add_ediv_of_dvd_left,
        Int.mul_ediv_cancel_left, show ((1 + 1) / 2 : Int) = 1 by decide, ← Int.sub_sub,
        Int.sub_eq_add_neg, Int.sub_eq_add_neg, Int.add_right_comm, Int.add_assoc q,
        show (1 + -1 : Int) = 0 by decide, Int.add_zero, ← Int.neg_mul]
      rw [Int.neg_eq_neg_one_mul]
      conv => rhs; congr; rw [← Int.one_mul q]
      rw [← Int.add_mul, show (1 + -2 : Int) = -1 by decide]
      apply Int.le_refl
      all_goals try decide
      all_goals try apply Int.dvd_mul_right

theorem bmod_lt {x : Int} {m : Nat} (h : 0 < m) : bmod x m < (m + 1) / 2 := by
  dsimp [bmod]
  split
  · assumption
  · apply Int.lt_of_lt_of_le
    · show _ < 0
      have : x % m < m := emod_lt_of_pos x (ofNat_pos.mpr h)
      exact Int.sub_neg_of_lt this
    · exact Int.le.intro_sub _ rfl

theorem bmod_le {x : Int} {m : Nat} (h : 0 < m) : bmod x m ≤ (m - 1) / 2 := by
  refine lt_add_one_iff.mp ?_
  calc
    bmod x m < (m + 1) / 2  := bmod_lt h
    _ = ((m + 1 - 2) + 2)/2 := by simp
    _ = (m - 1) / 2 + 1     := by
      rw [add_ediv_of_dvd_right]
      · simp (config := {decide := true}) only [Int.ediv_self]
        congr 2
        rw [Int.add_sub_assoc, ← Int.sub_neg]
        congr
      · trivial

-- This could be strengthed by changing to `w : x ≠ -1` if needed.
theorem bmod_natAbs_plus_one (x : Int) (w : 1 < x.natAbs) : bmod x (x.natAbs + 1) = - x.sign := by
  have t₁ : ∀ (x : Nat), x % (x + 2) = x :=
    fun x => Nat.mod_eq_of_lt (Nat.lt_succ_of_lt (Nat.lt.base x))
  have t₂ : ∀ (x : Int), 0 ≤ x → x % (x + 2) = x := fun x h => by
    match x, h with
    | Int.ofNat x, _ => erw [← Int.ofNat_two, ← ofNat_add, ← ofNat_emod, t₁]; rfl
  cases x with
  | ofNat x =>
    simp only [bmod, ofNat_eq_coe, natAbs_ofNat, natCast_add, ofNat_one,
      emod_self_add_one (ofNat_nonneg x)]
    match x with
    | 0 => rw [if_pos] <;> simp (config := {decide := true})
    | (x+1) =>
      rw [if_neg]
      · simp [← Int.sub_sub]
      · refine Int.not_lt.mpr ?_
        simp only [← natCast_add, ← ofNat_one, ← ofNat_two, ← ofNat_ediv]
        match x with
        | 0 => apply Int.le_refl
        | (x+1) =>
          refine Int.ofNat_le.mpr ?_
          apply Nat.div_le_of_le_mul
          simp only [Nat.two_mul, Nat.add_assoc]
          apply Nat.add_le_add_left (Nat.add_le_add_left (Nat.add_le_add_left (Nat.le_add_left
            _ _) _) _)
  | negSucc x =>
    rw [bmod, natAbs_negSucc, natCast_add, ofNat_one, sign_negSucc, Int.neg_neg,
      Nat.succ_eq_add_one, negSucc_emod]
    erw [t₂]
    · rw [natCast_add, ofNat_one, Int.add_sub_cancel, Int.add_comm, Int.add_sub_cancel, if_pos]
      · match x, w with
        | (x+1), _ =>
          rw [Int.add_assoc, add_ediv_of_dvd_right, show (1 + 1 : Int) = 2 by decide, Int.ediv_self]
          apply Int.lt_add_one_of_le
          rw [Int.add_comm, ofNat_add, Int.add_assoc, add_ediv_of_dvd_right,
            show ((1 : Nat) + 1 : Int) = 2 by decide, Int.ediv_self]
          apply Int.le_add_of_nonneg_left
          exact Int.le.intro_sub _ rfl
          all_goals decide
    · exact ofNat_nonneg x
    · exact succ_ofNat_pos (x + 1)

/-! ### `/` and ordering -/

protected theorem ediv_mul_le (a : Int) {b : Int} (H : b ≠ 0) : a / b * b ≤ a :=
  Int.le_of_sub_nonneg <| by rw [Int.mul_comm, ← emod_def]; apply emod_nonneg _ H

protected theorem ediv_le_of_le_mul {a b c : Int} (H : 0 < c) (H' : a ≤ b * c) : a / c ≤ b :=
  le_of_mul_le_mul_right (Int.le_trans (Int.ediv_mul_le _ (Int.ne_of_gt H)) H') H

protected theorem mul_lt_of_lt_ediv {a b c : Int} (H : 0 < c) (H3 : a < b / c) : a * c < b :=
  Int.lt_of_not_ge <| mt (Int.ediv_le_of_le_mul H) (Int.not_le_of_gt H3)

protected theorem mul_le_of_le_ediv {a b c : Int} (H1 : 0 < c) (H2 : a ≤ b / c) : a * c ≤ b :=
  Int.le_trans (Int.mul_le_mul_of_nonneg_right H2 (Int.le_of_lt H1))
    (Int.ediv_mul_le _ (Int.ne_of_gt H1))

protected theorem le_ediv_of_mul_le {a b c : Int} (H1 : 0 < c) (H2 : a * c ≤ b) : a ≤ b / c :=
  le_of_lt_add_one <|
    lt_of_mul_lt_mul_right (Int.lt_of_le_of_lt H2 (lt_ediv_add_one_mul_self _ H1)) (Int.le_of_lt H1)

protected theorem le_ediv_iff_mul_le {a b c : Int} (H : 0 < c) : a ≤ b / c ↔ a * c ≤ b :=
  ⟨Int.mul_le_of_le_ediv H, Int.le_ediv_of_mul_le H⟩

protected theorem ediv_le_ediv {a b c : Int} (H : 0 < c) (H' : a ≤ b) : a / c ≤ b / c :=
  Int.le_ediv_of_mul_le H (Int.le_trans (Int.ediv_mul_le _ (Int.ne_of_gt H)) H')

protected theorem ediv_lt_of_lt_mul {a b c : Int} (H : 0 < c) (H' : a < b * c) : a / c < b :=
  Int.lt_of_not_ge <| mt (Int.mul_le_of_le_ediv H) (Int.not_le_of_gt H')

protected theorem lt_mul_of_ediv_lt {a b c : Int} (H1 : 0 < c) (H2 : a / c < b) : a < b * c :=
  Int.lt_of_not_ge <| mt (Int.le_ediv_of_mul_le H1) (Int.not_le_of_gt H2)

protected theorem ediv_lt_iff_lt_mul {a b c : Int} (H : 0 < c) : a / c < b ↔ a < b * c :=
  ⟨Int.lt_mul_of_ediv_lt H, Int.ediv_lt_of_lt_mul H⟩

protected theorem le_mul_of_ediv_le {a b c : Int} (H1 : 0 ≤ b) (H2 : b ∣ a) (H3 : a / b ≤ c) :
    a ≤ c * b := by
  rw [← Int.ediv_mul_cancel H2]; exact Int.mul_le_mul_of_nonneg_right H3 H1

protected theorem lt_ediv_of_mul_lt {a b c : Int} (H1 : 0 ≤ b) (H2 : b ∣ c) (H3 : a * b < c) :
    a < c / b :=
  Int.lt_of_not_ge <| mt (Int.le_mul_of_ediv_le H1 H2) (Int.not_le_of_gt H3)

protected theorem lt_ediv_iff_mul_lt {a b : Int} (c : Int) (H : 0 < c) (H' : c ∣ b) :
    a < b / c ↔ a * c < b :=
  ⟨Int.mul_lt_of_lt_ediv H, Int.lt_ediv_of_mul_lt (Int.le_of_lt H) H'⟩

theorem ediv_pos_of_pos_of_dvd {a b : Int} (H1 : 0 < a) (H2 : 0 ≤ b) (H3 : b ∣ a) : 0 < a / b :=
  Int.lt_ediv_of_mul_lt H2 H3 (by rwa [Int.zero_mul])

theorem ediv_eq_ediv_of_mul_eq_mul {a b c d : Int}
    (H2 : d ∣ c) (H3 : b ≠ 0) (H4 : d ≠ 0) (H5 : a * d = b * c) : a / b = c / d :=
  Int.ediv_eq_of_eq_mul_right H3 <| by
    rw [← Int.mul_ediv_assoc _ H2]; exact (Int.ediv_eq_of_eq_mul_left H4 H5.symm).symm

/-!
### The following lemmas have been commented out here for a while, and need restoration.
-/

/-
theorem eq_mul_ediv_of_mul_eq_mul_of_dvd_left {a b c d : Int}
    (hb : b ≠ 0) (hbc : b ∣ c) (h : b * a = c * d) : a = c / b * d := by
  rcases hbc with ⟨k, hk⟩
  subst hk
  rw [Int.mul_ediv_cancel_left _ hb]
  rw [Int.mul_assoc] at h
  apply mul_left_cancel₀ hb h

/-- If an integer with larger absolute value divides an integer, it is
zero. -/
theorem eq_zero_of_dvd_ofNatAbs_lt_natAbs {a b : Int} (w : a ∣ b) (h : natAbs b < natAbs a) :
    b = 0 := by
  rw [← natAbs_dvd, ← dvd_natAbs, ofNat_dvd] at w
  rw [← natAbs_eq_zero]
  exact eq_zero_of_dvd_of_lt w h

theorem eq_zero_of_dvd_of_nonneg_of_lt {a b : Int} (w₁ : 0 ≤ a) (w₂ : a < b) (h : b ∣ a) : a = 0 :=
  eq_zero_of_dvd_ofNatAbs_lt_natAbs h (natAbs_lt_natAbs_of_nonneg_of_lt w₁ w₂)

/-- If two integers are congruent to a sufficiently large modulus,
they are equal. -/
theorem eq_of_mod_eq_ofNatAbs_sub_lt_natAbs {a b c : Int}
    (h1 : a % b = c) (h2 : natAbs (a - c) < natAbs b) : a = c :=
  Int.eq_of_sub_eq_zero (eq_zero_of_dvd_ofNatAbs_lt_natAbs (dvd_sub_of_emod_eq h1) h2)

theorem ofNat_add_negSucc_of_lt {m n : Nat} (h : m < n.succ) : ofNat m + -[n+1] = -[n+1 - m] := by
  change subNatNat _ _ = _
  have h' : n.succ - m = (n - m).succ
  apply succ_sub
  apply le_of_lt_succ h
  simp [*, subNatNat]

theorem ofNat_add_negSucc_of_ge {m n : Nat} (h : n.succ ≤ m) :
    ofNat m + -[n+1] = ofNat (m - n.succ) := by
  change subNatNat _ _ = _
  have h' : n.succ - m = 0
  apply tsub_eq_zero_iff_le.mpr h
  simp [*, subNatNat]

@[simp]
theorem neg_add_neg (m n : Nat) : -[m+1] + -[n+1] = -[Nat+1.succ (m + n)] :=
  rfl

theorem natAbs_le_of_dvd_ne_zero {s t : Int} (hst : s ∣ t) (ht : t ≠ 0) : natAbs s ≤ natAbs t :=
  not_lt.mp (mt (eq_zero_of_dvd_ofNatAbs_lt_natAbs hst) ht)

theorem natAbs_eq_of_dvd_dvd {s t : Int} (hst : s ∣ t) (hts : t ∣ s) : natAbs s = natAbs t :=
  Nat.dvd_antisymm (natAbs_dvd_iff_dvd.mpr hst) (natAbs_dvd_iff_dvd.mpr hts)

theorem div_dvd_of_dvd {s t : Int} (hst : s ∣ t) : t / s ∣ t := by
  rcases eq_or_ne s 0 with (rfl | hs)
  · simpa using hst
  rcases hst with ⟨c, hc⟩
  simp [hc, Int.mul_div_cancel_left _ hs]

theorem dvd_div_of_mul_dvd {a b c : Int} (h : a * b ∣ c) : b ∣ c / a := by
  rcases eq_or_ne a 0 with (rfl | ha)
  · simp only [Int.div_zero, dvd_zero]

  rcases h with ⟨d, rfl⟩
  refine' ⟨d, _⟩
  rw [mul_assoc, Int.mul_div_cancel_left _ ha]
-/

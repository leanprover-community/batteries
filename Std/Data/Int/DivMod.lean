/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Mario Carneiro
-/
import Std.Data.Int.Lemmas

/-!
# Lemmas about integer division
-/


open Nat

namespace Int

/-! ### `/`  -/

@[simp, norm_cast] theorem ofNat_div (m n : Nat) : ofNat (m / n) = ofNat m / ofNat n := rfl

theorem ofNat_fdiv : ∀ m n : Nat, ofNat (m / n) = (ofNat m).fdiv (ofNat n)
  | 0, _ => by simp [fdiv]
  | succ _, _ => rfl

theorem ofNat_ediv (m n : Nat) : ofNat (m / n) = (ofNat m).ediv (ofNat n) := rfl

theorem negSucc_ediv (m : Nat) {b : Int} (H : 0 < b) : -[m+1].ediv b = -(m / b + 1) :=
  match b, eq_succ_of_zero_lt H with
  | _, ⟨_, rfl⟩ => rfl

@[local simp] protected theorem zero_div : ∀ b : Int, 0 / b = 0
  | ofNat _ => show ofNat _ = _ by simp
  | -[_+1] => show -ofNat _ = _ by simp

@[simp] theorem zero_ediv : ∀ b : Int, ediv 0 b = 0
  | ofNat _ => show ofNat _ = _ by simp
  | -[_+1] => show -ofNat _ = _ by simp

@[simp] theorem zero_fdiv (b : Int) : fdiv 0 b = 0 := by cases b <;> rfl

-- Will be generalized to Euclidean domains.
@[local simp] protected theorem div_zero : ∀ a : Int, a / 0 = 0
  | ofNat _ => show ofNat _ = _ by simp
  | -[_+1] => rfl

@[simp] protected theorem ediv_zero : ∀ a : Int, ediv a 0 = 0
  | ofNat _ => show ofNat _ = _ by simp
  | -[_+1] => rfl

@[simp] protected theorem fdiv_zero : ∀ a : Int, fdiv a 0 = 0
  | 0      => rfl
  | succ _ => rfl
  | -[_+1] => rfl

theorem fdiv_eq_ediv : ∀ (a : Int) {b : Int}, 0 ≤ b → fdiv a b = ediv a b
  | 0, _, _ | -[_+1], 0, _ => by simp
  | succ _, ofNat _, _ | -[_+1], succ _, _ => rfl

theorem ediv_eq_div : ∀ {a b : Int}, 0 ≤ a → 0 ≤ b → ediv a b = a / b
  | 0, _, _, _ | _, 0, _, _ => by simp
  | succ _, succ _, _, _ => rfl

theorem fdiv_eq_div {a b : Int} (Ha : 0 ≤ a) (Hb : 0 ≤ b) : fdiv a b = a / b :=
  fdiv_eq_ediv _ Hb ▸ ediv_eq_div Ha Hb

@[simp] protected theorem div_neg : ∀ a b : Int, a / (-b) = -(a / b)
  | ofNat m, 0 => show ofNat (m / 0) = -↑(m / 0) by rw [Nat.div_zero] <;> rfl
  | ofNat m, -[n+1] | -[m+1], succ n => (Int.neg_neg _).symm
  | ofNat m, succ n | -[m+1], 0 | -[m+1], -[n+1] => rfl

@[simp] protected theorem ediv_neg : ∀ a b : Int, a.ediv (-b) = -(a.ediv b)
  | ofNat m, 0 => show ofNat (m / 0) = -↑(m / 0) by rw [Nat.div_zero] <;> rfl
  | ofNat m, -[n+1] => (Int.neg_neg _).symm
  | ofNat m, succ n | -[m+1], 0 | -[m+1], succ n | -[m+1], -[n+1] => rfl

protected theorem div_def (a b : Int) : a / b = Int.div a b := rfl

@[simp] protected theorem neg_div : ∀ a b : Int, (-a) / b = -(a / b)
  | 0, n => by simp [Int.neg_zero]
  | succ m, ofNat n | -[m+1], 0 | -[m+1], -[n+1] => rfl
  | succ m, -[n+1] | -[m+1], succ n => (Int.neg_neg _).symm

protected theorem neg_div_neg (a b : Int) : (-a) / (-b) = a / b := by
  simp [Int.div_neg, Int.neg_div, Int.neg_neg]

protected theorem div_nonneg {a b : Int} (Ha : 0 ≤ a) (Hb : 0 ≤ b) : 0 ≤ a / b :=
  match a, b, eq_ofNat_of_zero_le Ha, eq_ofNat_of_zero_le Hb with
  | _, _, ⟨_, rfl⟩, ⟨_, rfl⟩ => ofNat_zero_le _

theorem fdiv_nonneg {a b : Int} (Ha : 0 ≤ a) (Hb : 0 ≤ b) : 0 ≤ a.fdiv b :=
  match a, b, eq_ofNat_of_zero_le Ha, eq_ofNat_of_zero_le Hb with
  | _, _, ⟨_, rfl⟩, ⟨_, rfl⟩ => ofNat_fdiv .. ▸ ofNat_zero_le _

theorem ediv_nonneg {a b : Int} (Ha : 0 ≤ a) (Hb : 0 ≤ b) : 0 ≤ a.ediv b :=
  match a, b, eq_ofNat_of_zero_le Ha, eq_ofNat_of_zero_le Hb with
  | _, _, ⟨_, rfl⟩, ⟨_, rfl⟩ => ofNat_zero_le _

protected theorem div_nonpos {a b : Int} (Ha : 0 ≤ a) (Hb : b ≤ 0) : a / b ≤ 0 :=
  Int.nonpos_of_neg_nonneg <| Int.div_neg .. ▸ Int.div_nonneg Ha (Int.neg_nonneg_of_nonpos Hb)

theorem fdiv_nonpos : ∀ {a b : Int}, 0 ≤ a → b ≤ 0 → a.fdiv b ≤ 0
  | 0, 0, _, _ | 0, -[_+1], _, _ | succ _, 0, _, _ | succ _, -[_+1], _, _ => ⟨_⟩

theorem ediv_nonpos {a b : Int} (Ha : 0 ≤ a) (Hb : b ≤ 0) : a.ediv b ≤ 0 :=
  Int.nonpos_of_neg_nonneg <| Int.ediv_neg .. ▸ Int.ediv_nonneg Ha (Int.neg_nonneg_of_nonpos Hb)

theorem fdiv_neg' : ∀ {a b : Int}, a < 0 → 0 < b → a.fdiv b < 0
  | -[_+1], succ _, _, _ => negSucc_lt_zero _

theorem ediv_neg' {a b : Int} (Ha : a < 0) (Hb : 0 < b) : a.ediv b < 0 :=
  match a, b, eq_negSucc_of_lt_zero Ha, eq_succ_of_zero_lt Hb with
  | _, _, ⟨_, rfl⟩, ⟨_, rfl⟩ => negSucc_lt_zero _

@[simp] protected theorem div_one : ∀ a : Int, a / 1 = a
  | ofNat n => congrArg ofNat (Nat.div_one _)
  | -[n+1] => by simp [Int.div_def, Int.div, neg_ofNat_of_succ]

@[simp] theorem fdiv_one : ∀ a : Int, a.fdiv 1 = a
  | 0 => rfl
  | succ _ => congrArg ofNat (Nat.div_one _)
  | -[_+1] => congrArg negSucc (Nat.div_one _)

@[simp] theorem ediv_one : ∀ a : Int, a.ediv 1 = a
  | ofNat _ => congrArg ofNat (Nat.div_one _)
  | -[_+1] => congrArg negSucc (Nat.div_one _)

theorem div_eq_zero_of_lt {a b : Int} (H1 : 0 ≤ a) (H2 : a < b) : a / b = 0 :=
  match a, b, eq_ofNat_of_zero_le H1, eq_succ_of_zero_lt (Int.lt_of_le_of_lt H1 H2) with
  | _, _, ⟨_, rfl⟩, ⟨_, rfl⟩ => congrArg ofNat <| Nat.div_eq_of_lt <| ofNat_lt.1 H2

theorem ediv_eq_zero_of_lt {a b : Int} (H1 : 0 ≤ a) (H2 : a < b) : a.ediv b = 0 :=
  match a, b, eq_ofNat_of_zero_le H1, eq_succ_of_zero_lt (Int.lt_of_le_of_lt H1 H2) with
  | _, _, ⟨_, rfl⟩, ⟨_, rfl⟩ => congrArg ofNat <| Nat.div_eq_of_lt <| ofNat_lt.1 H2

theorem add_mul_ediv_right (a b : Int) {c : Int} (H : c ≠ 0) : (a + b * c).ediv c = a.ediv c + b :=
  suffices ∀ {{a b c : Int}}, 0 < c → (a + b * c).ediv c = a.ediv c + b from
    match Int.lt_trichotomy c 0 with
    | Or.inl hlt => by
      rw [← Int.neg_inj, ← Int.ediv_neg, Int.neg_add, ← Int.ediv_neg, ← Int.neg_mul_neg]
      exact this (Int.neg_pos_of_neg hlt)
    | Or.inr (Or.inl HEq) => absurd HEq H
    | Or.inr (Or.inr hgt) => this hgt
  suffices ∀ {k n : Nat} {a : Int}, (a + n * k.succ).ediv k.succ = a.ediv k.succ + n from
    fun a b c H => match c, eq_succ_of_zero_lt H, b with
      | _, ⟨_, rfl⟩, ofNat _ => this
      | _, ⟨k, rfl⟩, -[n+1] => show (a - n.succ * k.succ).ediv k.succ = a.ediv k.succ - n.succ by
        rw [← Int.add_sub_cancel (ediv ..), ← this, Int.sub_add_cancel]
  fun {k n} => @fun
  | ofNat m => congrArg ofNat <| Nat.add_mul_div_right _ _ k.succ_pos
  | -[m+1] => by
    show ((n * k.succ : Nat) - m.succ : Int).ediv k.succ = n - (m / k.succ + 1 : Nat)
    if h : m < n * k.succ then
      rw [← Int.ofNat_sub h, ← Int.ofNat_sub ((Nat.div_lt_iff_lt_mul k.succ_pos).2 h)]
      apply congrArg ofNat
      rw [Nat.mul_comm, Nat.mul_sub_div]; rwa [Nat.mul_comm]
    else
      have h := Nat.not_lt.1 h
      have H {a b : Nat} (h : a ≤ b) : (a : Int) + -((b : Int) + 1) = -[b - a +1] := by
        rw [negSucc_ofNat_eq, Int.ofNat_sub h]
        simp only [Int.sub_eq_add_neg, Int.neg_add, Int.neg_neg, Int.add_left_comm, Int.add_assoc]
      show ediv (↑(n * succ k) + -((m : Int) + 1)) (succ k) = n + -(↑(m / succ k) + 1 : Int)
      rw [H h, H ((Nat.le_div_iff_mul_le k.succ_pos).2 h)]
      apply congrArg negSucc
      rw [Nat.mul_comm, Nat.sub_mul_div]; rwa [Nat.mul_comm]

theorem add_mul_ediv_left (a : Int) {b : Int}
    (c : Int) (H : b ≠ 0) : (a + b * c).ediv b = a.ediv b + c :=
  Int.mul_comm .. ▸ Int.add_mul_ediv_right _ _ H

theorem add_ediv_of_dvd_right {a b c : Int} (H : c ∣ b) : (a + b).ediv c = a.ediv c + b.ediv c :=
  if h : c = 0 then by simp [h] else by
    let ⟨k, hk⟩ := H
    rw [hk, Int.mul_comm c k, Int.add_mul_ediv_right _ _ h,
      ← Int.zero_add (k * c), Int.add_mul_ediv_right _ _ h, Int.zero_ediv, Int.zero_add]

theorem add_ediv_of_dvd_left {a b c : Int} (H : c ∣ a) : (a + b).ediv c = a.ediv c + b.ediv c := by
  rw [Int.add_comm, Int.add_ediv_of_dvd_right H, Int.add_comm]

@[simp] theorem mul_ediv_cancel (a : Int) {b : Int} (H : b ≠ 0) : ediv (a * b) b = a := by
  have := Int.add_mul_ediv_right 0 a H
  rwa [Int.zero_add, Int.zero_ediv, Int.zero_add] at this

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

@[simp] protected theorem mul_div_cancel (a : Int) {b : Int} (H : b ≠ 0) : a * b / b = a :=
  have : ∀ {a b : Nat}, (b : Int) ≠ 0 → (a * b / b : Int) = a := fun H => by
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

@[simp] protected theorem mul_div_cancel_left (b : Int) (H : a ≠ 0) : a * b / a = b :=
  Int.mul_comm .. ▸ Int.mul_div_cancel _ H

@[simp] theorem mul_fdiv_cancel_left (b : Int) (H : a ≠ 0) : fdiv (a * b) a = b :=
  Int.mul_comm .. ▸ Int.mul_fdiv_cancel _ H

@[simp] theorem mul_ediv_cancel_left (b : Int) (H : a ≠ 0) : ediv (a * b) a = b :=
  Int.mul_comm .. ▸ Int.mul_ediv_cancel _ H

@[simp] protected theorem div_self {a : Int} (H : a ≠ 0) : a / a = 1 := by
  have := Int.mul_div_cancel 1 H; rwa [Int.one_mul] at this

@[simp] protected theorem fdiv_self {a : Int} (H : a ≠ 0) : a.fdiv a = 1 := by
  have := Int.mul_fdiv_cancel 1 H; rwa [Int.one_mul] at this

@[simp] protected theorem ediv_self {a : Int} (H : a ≠ 0) : a.ediv a = 1 := by
  have := Int.mul_ediv_cancel 1 H; rwa [Int.one_mul] at this

/-! ### mod -/

theorem mod_def' (m n : Int) : m % n = mod m n := rfl

@[simp, norm_cast] theorem ofNat_mod (m n : Nat) : ofNat (m % n) = m % n := rfl

theorem ofNat_fmod (m n : Nat) : ofNat (m % n) = fmod m n := by cases m <;> simp [fmod]

theorem ofNat_emod (m n : Nat) : ofNat (m % n) = emod m n := rfl

theorem negSucc_emod (m : Nat) {b : Int} (bpos : 0 < b) : -[m+1].emod b = b - 1 - emod m b := by
  rw [Int.sub_sub, Int.add_comm]
  match b, eq_succ_of_zero_lt bpos with
  | _, ⟨n, rfl⟩ => rfl

@[simp] theorem zero_mod (b : Int) : 0 % b = 0 := by cases b <;> simp [mod_def', mod]

@[simp] theorem zero_fmod (b : Int) : fmod 0 b = 0 := by cases b <;> rfl

@[simp] theorem zero_emod (b : Int) : emod 0 b = 0 := by simp [emod]

@[simp] theorem mod_zero : ∀ a : Int, a % 0 = a
  | ofNat _ => congrArg ofNat <| Nat.mod_zero _
  | -[_+1] => rfl

@[simp] theorem fmod_zero : ∀ a : Int, fmod a 0 = a
  | 0 => rfl
  | succ _ => congrArg ofNat <| Nat.mod_zero _
  | -[_+1]  => congrArg negSucc <| Nat.mod_zero _

@[simp] theorem emod_zero : ∀ a : Int, emod a 0 = a
  | ofNat _ => congrArg ofNat <| Nat.mod_zero _
  | -[_+1]  => congrArg negSucc <| Nat.mod_zero _

theorem mod_add_div : ∀ a b : Int, a % b + b * (a / b) = a
  | ofNat _, ofNat _ => congrArg ofNat (Nat.mod_add_div ..)
  | ofNat m, -[n+1] => by
    show (m % succ n + -↑(succ n) * -↑(m / succ n) : Int) = m
    rw [Int.neg_mul_neg] <;> exact congrArg ofNat (Nat.mod_add_div ..)
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

theorem emod_add_ediv : ∀ a b : Int, a.emod b + b * a.ediv b = a
  | ofNat _, ofNat _ => congrArg ofNat <| Nat.mod_add_div ..
  | ofNat m, -[n+1] => by
    show (m % succ n + -↑(succ n) * -↑(m / succ n) : Int) = m
    rw [Int.neg_mul_neg]; exact congrArg ofNat <| Nat.mod_add_div ..
  | -[_+1], 0 => by rw [emod_zero]; rfl
  | -[m+1], succ n => aux m n.succ
  | -[m+1], -[n+1] => aux m n.succ
where
  aux (m n : Nat) : n - (emod m n + 1) - (n * ediv m n + n) = -[m+1] := by
    rw [← ofNat_emod, ← ofNat_ediv, ← Int.sub_sub, negSucc_ofNat_eq, Int.sub_sub n,
      ← Int.neg_neg (_-_), Int.neg_sub, Int.sub_sub_self, Int.add_right_comm]
    exact congrArg (fun x => -(ofNat x + 1)) (Nat.mod_add_div ..)

theorem div_add_mod (a b : Int) : b * (a / b) + a % b = a :=
  (Int.add_comm ..).trans (mod_add_div ..)

theorem fdiv_add_fmod (a b : Int) : b * (a.fdiv b) + a.fmod b = a :=
  (Int.add_comm ..).trans (fmod_add_fdiv ..)

theorem ediv_add_emod (a b : Int) : b * (a.ediv b) + a.emod b = a :=
  (Int.add_comm ..).trans (emod_add_ediv ..)

theorem mod_def (a b : Int) : a % b = a - b * (a / b) := by
  rw [← Int.add_sub_cancel (a % b), mod_add_div]

theorem fmod_def (a b : Int) : a.fmod b = a - b * (a.fdiv b) := by
  rw [← Int.add_sub_cancel (a.fmod b), fmod_add_fdiv]

theorem emod_def (a b : Int) : a.emod b = a - b * (a.ediv b) := by
  rw [← Int.add_sub_cancel (a.emod b), emod_add_ediv]

theorem fmod_eq_emod (a : Int) {b : Int} (hb : 0 ≤ b) : fmod a b = emod a b := by
  simp [fmod_def, emod_def, fdiv_eq_ediv _ hb]

theorem emod_eq_mod {a b : Int} (ha : 0 ≤ a) (hb : 0 ≤ b) : emod a b = a % b := by
  simp [emod_def, mod_def, ediv_eq_div ha hb]

theorem fmod_eq_mod {a b : Int} (Ha : 0 ≤ a) (Hb : 0 ≤ b) : fmod a b = a % b :=
  fmod_eq_emod _ Hb ▸ emod_eq_mod Ha Hb

@[simp] theorem mod_neg (a b : Int) : a % -b = a % b := by
  rw [mod_def, mod_def, Int.div_neg, Int.neg_mul_neg]

@[simp] theorem emod_neg (a b : Int) : a.emod (-b) = a.emod b := by
  rw [emod_def, emod_def, Int.ediv_neg, Int.neg_mul_neg]

@[local simp] theorem mod_one (a : Int) : a % 1 = 0 := by
  simp [mod_def, Int.div_one, Int.one_mul, Int.sub_self]

@[simp] theorem emod_one (a : Int) : a.emod 1 = 0 := by
  simp [emod_def, Int.one_mul, Int.sub_self]

@[simp] theorem fmod_one (a : Int) : a.fmod 1 = 0 := by
  simp [fmod_def, Int.one_mul, Int.sub_self]

theorem mod_eq_of_lt {a b : Int} (H1 : 0 ≤ a) (H2 : a < b) : a % b = a :=
  have b0 := Int.le_trans H1 (Int.le_of_lt H2)
  match a, b, eq_ofNat_of_zero_le H1, eq_ofNat_of_zero_le b0 with
  | _, _, ⟨_, rfl⟩, ⟨_, rfl⟩ => congrArg ofNat <| Nat.mod_eq_of_lt (Int.ofNat_lt.1 H2)

theorem fmod_eq_of_lt {a b : Int} (H1 : 0 ≤ a) (H2 : a < b) : a.fmod b = a := by
  rw [fmod_eq_mod H1 (Int.le_trans H1 (Int.le_of_lt H2)), mod_eq_of_lt H1 H2]

theorem emod_eq_of_lt {a b : Int} (H1 : 0 ≤ a) (H2 : a < b) : a.emod b = a := by
  rw [emod_eq_mod H1 (Int.le_trans H1 (Int.le_of_lt H2)), mod_eq_of_lt H1 H2]

theorem mod_nonneg : ∀ {a : Int} (b : Int), 0 ≤ a → 0 ≤ a % b
  | ofNat _, -[_+1], _ | ofNat _, ofNat _, _ => ofNat_nonneg _

theorem emod_nonneg : ∀ (a : Int) {b : Int}, b ≠ 0 → 0 ≤ a.emod b
  | ofNat _, _, _ => ofNat_zero_le _
  | -[_+1], _, H => Int.sub_nonneg_of_le <| ofNat_le.2 <| Nat.mod_lt _ (natAbs_pos.2 H)

theorem fmod_nonneg {a b : Int} (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a.fmod b :=
  fmod_eq_mod ha hb ▸ mod_nonneg _ ha

theorem mod_lt_of_pos (a : Int) {b : Int} (H : 0 < b) : a % b < b :=
  match a, b, eq_succ_of_zero_lt H with
  | ofNat _, _, ⟨n, rfl⟩ => ofNat_lt.2 <| Nat.mod_lt _ n.succ_pos
  | -[_+1], _, ⟨n, rfl⟩ => Int.lt_of_le_of_lt
    (Int.neg_nonpos_of_nonneg <| Int.ofNat_nonneg _) (ofNat_pos.2 n.succ_pos)

theorem emod_lt_of_pos (a : Int) {b : Int} (H : 0 < b) : a.emod b < b :=
  match a, b, eq_succ_of_zero_lt H with
  | ofNat m, _, ⟨n, rfl⟩ => ofNat_lt.2 (Nat.mod_lt _ (Nat.succ_pos _))
  | -[m+1], _, ⟨n, rfl⟩ => by
    simp [emod, Int.subNatNat_eq_coe]
    exact Int.sub_lt_self _ (ofNat_lt.2 <| Nat.succ_pos _)

theorem fmod_lt_of_pos (a : Int) {b : Int} (H : 0 < b) : a.fmod b < b :=
  fmod_eq_emod _ (Int.le_of_lt H) ▸ emod_lt_of_pos a H

theorem mod_add_div' (m k : Int) : m % k + m / k * k = m := by
  rw [Int.mul_comm]; apply mod_add_div

theorem div_add_mod' (m k : Int) : m / k * k + m % k = m := by
  rw [Int.mul_comm]; apply div_add_mod

theorem emod_add_ediv' (m k : Int) : m.emod k + m.ediv k * k = m := by
  rw [Int.mul_comm]; apply emod_add_ediv

theorem ediv_add_emod' (m k : Int) : m.ediv k * k + m.emod k = m := by
  rw [Int.mul_comm]; apply ediv_add_emod

@[simp] theorem add_mul_emod_self {a b c : Int} : (a + b * c).emod c = a.emod c :=
  if cz : c = 0 then by
    rw [cz, Int.mul_zero, Int.add_zero]
  else by
    rw [Int.emod_def, Int.emod_def, Int.add_mul_ediv_right _ _ cz, Int.add_comm _ b,
      Int.mul_add, Int.mul_comm, ← Int.sub_sub, Int.add_sub_cancel]

@[simp] theorem add_mul_emod_self_left (a b c : Int) : (a + b * c).emod b = a.emod b := by
  rw [Int.mul_comm, Int.add_mul_emod_self]

@[simp] theorem add_emod_self {a b : Int} : (a + b).emod b = a.emod b := by
  have := add_mul_emod_self_left a b 1; rwa [Int.mul_one] at this

@[simp] theorem add_emod_self_left {a b : Int} : (a + b).emod a = b.emod a := by
  rw [Int.add_comm, Int.add_emod_self]

@[simp] theorem emod_add_emod (m n k : Int) : (m.emod n + k).emod n = (m + k).emod n := by
  have := (add_mul_emod_self_left (m.emod n + k) n (m.ediv n)).symm
  rwa [Int.add_right_comm, emod_add_ediv] at this

@[simp] theorem add_emod_emod (m n k : Int) : (m + n.emod k).emod k = (m + n).emod k := by
  rw [Int.add_comm, emod_add_emod, Int.add_comm]

theorem add_emod (a b n : Int) : (a + b).emod n = (a.emod n + b.emod n).emod n := by
  rw [add_emod_emod, emod_add_emod]

theorem add_emod_eq_add_emod_right {m n k : Int} (i : Int)
    (H : m.emod n = k.emod n) : (m + i).emod n = (k + i).emod n := by
  rw [← emod_add_emod, ← emod_add_emod k, H]

theorem add_emod_eq_add_emod_left {m n k : Int} (i : Int)
    (H : m.emod n = k.emod n) : (i + m).emod n = (i + k).emod n := by
  rw [Int.add_comm, add_emod_eq_add_emod_right _ H, Int.add_comm]

theorem emod_add_cancel_right {m n k : Int} (i) : (m + i).emod n = (k + i).emod n ↔ m.emod n = k.emod n :=
  ⟨fun H => by
    have := add_emod_eq_add_emod_right (-i) H
    rwa [Int.add_neg_cancel_right, Int.add_neg_cancel_right] at this,
  add_emod_eq_add_emod_right _⟩

theorem emod_add_cancel_left {m n k i : Int} : (i + m).emod n = (i + k).emod n ↔ m.emod n = k.emod n := by
  rw [Int.add_comm, Int.add_comm i, emod_add_cancel_right]

theorem emod_sub_cancel_right {m n k : Int} (i) : (m - i).emod n = (k - i).emod n ↔ m.emod n = k.emod n :=
  emod_add_cancel_right _

theorem emod_eq_emod_iff_emod_sub_eq_zero {m n k : Int} : m.emod n = k.emod n ↔ (m - k).emod n = 0 :=
  (emod_sub_cancel_right k).symm.trans <| by simp [Int.sub_self]

@[simp] theorem mul_mod_left (a b : Int) : (a * b) % b = 0 :=
  if h : b = 0 then by simp [h, Int.mul_zero] else by
    rw [Int.mod_def, Int.mul_div_cancel _ h, Int.mul_comm, Int.sub_self]

@[simp] theorem mul_fmod_left (a b : Int) : (a * b).fmod b = 0 :=
  if h : b = 0 then by simp [h, Int.mul_zero] else by
    rw [Int.fmod_def, Int.mul_fdiv_cancel _ h, Int.mul_comm, Int.sub_self]

@[simp] theorem mul_emod_left (a b : Int) : (a * b).emod b = 0 := by
  rw [← Int.zero_add (a * b), Int.add_mul_emod_self, Int.zero_emod]

@[simp] theorem mul_mod_right (a b : Int) : a * b % a = 0 := by
  rw [Int.mul_comm, mul_mod_left]

@[simp] theorem mul_fmod_right (a b : Int) : (a * b).fmod a = 0 := by
  rw [Int.mul_comm, mul_fmod_left]

@[simp] theorem mul_emod_right (a b : Int) : (a * b).emod a = 0 := by
  rw [Int.mul_comm, mul_emod_left]

theorem mul_emod (a b n : Int) : (a * b).emod n = (a.emod n * b.emod n).emod n := by
  conv => lhs; rw [
    ← emod_add_ediv a n, ← emod_add_ediv' b n, Int.add_mul, Int.mul_add, Int.mul_add,
    Int.mul_assoc, Int.mul_assoc, ← Int.mul_add n _ _, add_mul_emod_self_left,
    ← Int.mul_assoc, add_mul_emod_self]

@[local simp] theorem mod_self {a : Int} : a % a = 0 := by
  have := mul_mod_left 1 a; rwa [Int.one_mul] at this

@[simp] theorem fmod_self {a : Int} : a.fmod a = 0 := by
  have := mul_fmod_left 1 a; rwa [Int.one_mul] at this

@[simp] theorem emod_self {a : Int} : a.emod a = 0 := by
  have := mul_emod_left 1 a; rwa [Int.one_mul] at this

@[simp] theorem emod_emod_of_dvd (n : Int) {m k : Int}
    (h : m ∣ k) : (n.emod k).emod m = n.emod m := by
  conv => rhs; rw [← emod_add_ediv n k]
  match k, h with
  | _, ⟨t, rfl⟩ => rw [Int.mul_assoc, add_mul_emod_self_left]

@[simp] theorem emod_emod (a b : Int) : (a.emod b).emod b = a.emod b := by
  conv => rhs; rw [← emod_add_ediv a b, add_mul_emod_self_left]

theorem sub_emod (a b n : Int) : (a - b).emod n = (a.emod n - b.emod n).emod n := by
  apply (emod_add_cancel_right b).mp
  rw [Int.sub_add_cancel, ← Int.add_emod_emod, Int.sub_add_cancel, emod_emod]

protected theorem ediv_emod_unique {a b r q : Int} (h : 0 < b) :
  a.ediv b = q ∧ a.emod b = r ↔ r + b * q = a ∧ 0 ≤ r ∧ r < b := by
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
    (b c : Int) (H : 0 < a) : (a * b).ediv (a * c) = b.ediv c :=
  suffices ∀ (m k : Nat) (b : Int), (m.succ * b).ediv (m.succ * k) = b.ediv k from
    match a, eq_succ_of_zero_lt H, c, Int.eq_nat_or_neg c with
    | _, ⟨m, rfl⟩, _, ⟨k, .inl rfl⟩ => this _ ..
    | _, ⟨m, rfl⟩, _, ⟨k, .inr rfl⟩ => by
      rw [Int.mul_neg, Int.ediv_neg, Int.ediv_neg]; apply congrArg Neg.neg; apply this
  fun m k b =>
  match b, k with
  | ofNat n, k => congrArg ofNat (Nat.mul_div_mul _ _ m.succ_pos)
  | -[n+1], 0 => by
    rw [Int.ofNat_zero, Int.mul_zero, Int.ediv_zero, Int.ediv_zero]
  | -[n+1], succ k => congrArg negSucc <|
    show (m.succ * n + m) / (m.succ * k.succ) = n / k.succ by
      apply Nat.div_eq_of_lt_le
      · refine Nat.le_trans ?_ (Nat.le_add_right _ _)
        rw [← Nat.mul_div_mul _ _ m.succ_pos]
        apply Nat.div_mul_le_self
      · show m.succ * n.succ ≤ _
        rw [Nat.mul_left_comm]
        apply Nat.mul_le_mul_left
        apply (Nat.div_lt_iff_lt_mul k.succ_pos).1
        apply Nat.lt_succ_self


@[simp] theorem mul_ediv_mul_of_pos_left
    (a : Int) {b : Int} (c : Int) (H : 0 < b) : (a * b).ediv (c * b) = a.ediv c := by
  rw [Int.mul_comm, Int.mul_comm c, mul_ediv_mul_of_pos _ _ H]

@[simp] theorem mul_emod_mul_of_pos
    {a : Int} (b c : Int) (H : 0 < a) : (a * b).emod (a * c) = a * (b.emod c) := by
  rw [emod_def, emod_def, mul_ediv_mul_of_pos _ _ H, Int.mul_sub, Int.mul_assoc]

theorem lt_div_add_one_mul_self (a : Int) {b : Int} (H : 0 < b) : a < (a / b + 1) * b := by
  rw [Int.add_mul, Int.one_mul, Int.mul_comm]
  exact Int.lt_add_of_sub_left_lt <| Int.mod_def .. ▸ mod_lt_of_pos _ H

theorem lt_ediv_add_one_mul_self (a : Int) {b : Int} (H : 0 < b) : a < (a.ediv b + 1) * b := by
  rw [Int.add_mul, Int.one_mul, Int.mul_comm]
  exact Int.lt_add_of_sub_left_lt <| Int.emod_def .. ▸ emod_lt_of_pos _ H

theorem lt_fdiv_add_one_mul_self (a : Int) {b : Int} (H : 0 < b) : a < (a.fdiv b + 1) * b :=
  Int.fdiv_eq_ediv _ (Int.le_of_lt H) ▸ lt_ediv_add_one_mul_self a H

@[simp] theorem natAbs_div (a b : Int) : natAbs (a / b) = natAbs a / natAbs b :=
  match a, b, eq_nat_or_neg a, eq_nat_or_neg b with
  | _, _, ⟨_, .inl rfl⟩, ⟨_, .inl rfl⟩ => rfl
  | _, _, ⟨_, .inl rfl⟩, ⟨_, .inr rfl⟩ => by rw [Int.div_neg, natAbs_neg, natAbs_neg]; rfl
  | _, _, ⟨_, .inr rfl⟩, ⟨_, .inl rfl⟩ => by rw [Int.neg_div, natAbs_neg, natAbs_neg]; rfl
  | _, _, ⟨_, .inr rfl⟩, ⟨_, .inr rfl⟩ => by rw [Int.neg_div_neg, natAbs_neg, natAbs_neg]; rfl

theorem natAbs_div_le_natAbs (a b : Int) : natAbs (a.ediv b) ≤ natAbs a :=
  match b, eq_nat_or_neg b with
  | _, ⟨n, .inl rfl⟩ => aux _ _
  | _, ⟨n, .inr rfl⟩ => by rw [Int.ediv_neg, natAbs_neg]; apply aux
where
  aux : ∀ (a : Int) (n : Nat), natAbs (a.ediv n) ≤ natAbs a
  | ofNat _, _ => Nat.div_le_self ..
  | -[_+1], 0 => Nat.zero_le _
  | -[_+1], succ _ => Nat.succ_le_succ (Nat.div_le_self _ _)

theorem ediv_le_self {a : Int} (b : Int) (Ha : 0 ≤ a) : a.ediv b ≤ a := by
  have := Int.le_trans le_natAbs (ofNat_le.2 <| natAbs_div_le_natAbs a b)
  rwa [natAbs_of_nonneg Ha] at this

theorem mul_div_cancel_of_mod_eq_zero {a b : Int} (H : a % b = 0) : b * (a / b) = a := by
  have := mod_add_div a b; rwa [H, Int.zero_add] at this

theorem div_mul_cancel_of_mod_eq_zero {a b : Int} (H : a % b = 0) : a / b * b = a := by
  rw [Int.mul_comm, mul_div_cancel_of_mod_eq_zero H]

theorem mul_ediv_cancel_of_emod_eq_zero {a b : Int} (H : a.emod b = 0) : b * (a.ediv b) = a := by
  have := emod_add_ediv a b; rwa [H, Int.zero_add] at this

theorem ediv_mul_cancel_of_emod_eq_zero {a b : Int} (H : a.emod b = 0) : a.ediv b * b = a := by
  rw [Int.mul_comm, mul_ediv_cancel_of_emod_eq_zero H]

/-! ### dvd -/

protected theorem dvd_zero (n : Int) : n ∣ 0 := ⟨0, (Int.mul_zero _).symm⟩

protected theorem dvd_refl (n : Int) : n ∣ n := ⟨1, (Int.mul_one _).symm⟩

protected theorem dvd_trans : ∀ {a b c : Int}, a ∣ b → b ∣ c → a ∣ c
  | _, _, _, ⟨d, rfl⟩, ⟨e, rfl⟩ => ⟨d * e, by rw [Int.mul_assoc]⟩

protected theorem zero_dvd {n : Int} : 0 ∣ n ↔ n = 0 :=
  ⟨fun ⟨k, e⟩ => by rw [e, Int.zero_mul], fun h => h.symm ▸ Int.dvd_refl _⟩

protected theorem neg_dvd {a b : Int} : -a ∣ b ↔ a ∣ b := by
  constructor <;> exact fun ⟨k, e⟩ =>
    ⟨-k, by simp [e, Int.neg_mul, Int.mul_neg, Int.neg_neg]⟩

protected theorem dvd_neg {a b : Int} : a ∣ -b ↔ a ∣ b := by
  constructor <;> exact fun ⟨k, e⟩ =>
    ⟨-k, by simp [← e, Int.neg_mul, Int.mul_neg, Int.neg_neg]⟩

protected theorem dvd_mul_right (a b : Int) : a ∣ a * b := ⟨_, rfl⟩

protected theorem dvd_mul_left (a b : Int) : b ∣ a * b := ⟨_, Int.mul_comm ..⟩

protected theorem dvd_add : ∀ {a b c : Int}, a ∣ b → a ∣ c → a ∣ b + c
  | _, _, _, ⟨d, rfl⟩, ⟨e, rfl⟩ => ⟨d + e, by rw [Int.mul_add]⟩

protected theorem dvd_sub : ∀ {a b c : Int}, a ∣ b → a ∣ c → a ∣ b - c
  | _, _, _, ⟨d, rfl⟩, ⟨e, rfl⟩ => ⟨d - e, by rw [Int.mul_sub]⟩

protected theorem dvd_add_left {a b c : Int} (H : a ∣ c) : a ∣ b + c ↔ a ∣ b :=
  ⟨fun h => by have := Int.dvd_sub h H; rwa [Int.add_sub_cancel] at this, (Int.dvd_add · H)⟩

protected theorem dvd_add_right {a b c : Int} (H : a ∣ b) : a ∣ b + c ↔ a ∣ c := by
  rw [Int.add_comm, Int.dvd_add_left H]

protected theorem dvd_iff_dvd_of_dvd_sub {a b c : Int} (H : a ∣ b - c) : a ∣ b ↔ a ∣ c :=
  ⟨fun h => Int.sub_sub_self b c ▸ Int.dvd_sub h H,
   fun h => Int.sub_add_cancel b c ▸ Int.dvd_add H h⟩

protected theorem dvd_iff_dvd_of_dvd_add {a b c : Int} (H : a ∣ b + c) : a ∣ b ↔ a ∣ c := by
  rw [← Int.sub_neg] at H; rw [Int.dvd_iff_dvd_of_dvd_sub H, Int.dvd_neg]

@[norm_cast] theorem ofNat_dvd {m n : Nat} : (↑m : Int) ∣ ↑n ↔ m ∣ n := by
  refine ⟨fun ⟨a, ae⟩ => ?_, fun ⟨k, e⟩ => ⟨k, by rw [e, Int.ofNat_mul]⟩⟩
  match Int.le_total a 0 with
  | .inl h =>
    have := ae.symm ▸ Int.mul_nonpos_of_nonneg_of_nonpos (ofNat_zero_le _) h
    rw [Nat.le_antisymm (ofNat_le.1 this) (Nat.zero_le _)]
    apply Nat.dvd_zero
  | .inr h => match a, eq_ofNat_of_zero_le h with
    | _, ⟨k, rfl⟩ => exact ⟨k, Int.ofNat.inj ae⟩

@[simp] theorem natAbs_dvd_natAbs {a b : Int} : natAbs a ∣ natAbs b ↔ a ∣ b := by
  refine ⟨fun ⟨k, hk⟩ => ?_, fun ⟨k, hk⟩ => ⟨natAbs k, hk.symm ▸ natAbs_mul a k⟩⟩
  rw [← natAbs_ofNat k, ← natAbs_mul, natAbs_eq_natAbs_iff] at hk
  cases hk <;> subst b
  · apply Int.dvd_mul_right
  · rw [← Int.mul_neg]; apply Int.dvd_mul_right

theorem natAbs_dvd {a b : Int} : (a.natAbs : Int) ∣ b ↔ a ∣ b :=
  match natAbs_eq a with
  | .inl e => by rw [← e]
  | .inr e => by rw [← Int.neg_dvd, ← e]

theorem dvd_natAbs {a b : Int} : a ∣ b.natAbs ↔ a ∣ b :=
  match natAbs_eq b with
  | .inl e => by rw [← e]
  | .inr e => by rw [← Int.dvd_neg, ← e]

theorem ofNat_dvd_left {n : Nat} {z : Int} : (↑n : Int) ∣ z ↔ n ∣ z.natAbs := by
  rw [← natAbs_dvd_natAbs, natAbs_ofNat]

theorem ofNat_dvd_right {n : Nat} {z : Int} : z ∣ (↑n : Int) ↔ z.natAbs ∣ n := by
  rw [← natAbs_dvd_natAbs, natAbs_ofNat]

theorem dvd_antisymm {a b : Int} (H1 : 0 ≤ a) (H2 : 0 ≤ b) : a ∣ b → b ∣ a → a = b := by
  rw [← natAbs_of_nonneg H1, ← natAbs_of_nonneg H2]
  rw [ofNat_dvd, ofNat_dvd, ofNat_inj]
  apply Nat.dvd_antisymm

theorem dvd_of_mod_eq_zero {a b : Int} (H : b % a = 0) : a ∣ b :=
  ⟨b / a, (mul_div_cancel_of_mod_eq_zero H).symm⟩

theorem dvd_of_emod_eq_zero {a b : Int} (H : b.emod a = 0) : a ∣ b :=
  ⟨b.ediv a, (mul_ediv_cancel_of_emod_eq_zero H).symm⟩

theorem mod_eq_zero_of_dvd : ∀ {a b : Int}, a ∣ b → b % a = 0
  | _, _, ⟨_, rfl⟩ => mul_mod_right ..

theorem emod_eq_zero_of_dvd : ∀ {a b : Int}, a ∣ b → b.emod a = 0
  | _, _, ⟨_, rfl⟩ => mul_emod_right ..

theorem dvd_iff_mod_eq_zero (a b : Int) : a ∣ b ↔ b % a = 0 :=
  ⟨mod_eq_zero_of_dvd, dvd_of_mod_eq_zero⟩

theorem dvd_iff_emod_eq_zero (a b : Int) : a ∣ b ↔ b.emod a = 0 :=
  ⟨emod_eq_zero_of_dvd, dvd_of_emod_eq_zero⟩

instance decidableDvd : DecidableRel (α := Int) (· ∣ ·) := fun _ _ =>
  decidable_of_decidable_of_iff (dvd_iff_mod_eq_zero ..).symm

/-- If `a % b = c` then `b` divides `a - c`. -/
theorem dvd_sub_of_emod_eq {a b c : Int} (h : a.emod b = c) : b ∣ a - c := by
  have hx : (a.emod b).emod b = c.emod b := by
    rw [h]
  rw [Int.emod_emod, ← emod_sub_cancel_right c, Int.sub_self, zero_emod] at hx
  exact dvd_of_emod_eq_zero hx

protected theorem div_mul_cancel {a b : Int} (H : b ∣ a) : a / b * b = a :=
  div_mul_cancel_of_mod_eq_zero (mod_eq_zero_of_dvd H)

protected theorem ediv_mul_cancel {a b : Int} (H : b ∣ a) : a.ediv b * b = a :=
  ediv_mul_cancel_of_emod_eq_zero (emod_eq_zero_of_dvd H)

protected theorem mul_div_cancel' {a b : Int} (H : a ∣ b) : a * (b / a) = b := by
  rw [Int.mul_comm, Int.div_mul_cancel H]

protected theorem mul_ediv_cancel' {a b : Int} (H : a ∣ b) : a * (b.ediv a) = b := by
  rw [Int.mul_comm, Int.ediv_mul_cancel H]

protected theorem mul_div_assoc (a : Int) : ∀ {b c : Int}, c ∣ b → a * b / c = a * (b / c)
  | _, c, ⟨d, rfl⟩ =>
    if cz : c = 0 then by simp [cz, Int.mul_zero] else by
      rw [Int.mul_left_comm, Int.mul_div_cancel_left _ cz, Int.mul_div_cancel_left _ cz]

protected theorem mul_ediv_assoc (a : Int) : ∀ {b c : Int}, c ∣ b → (a * b).ediv c = a * b.ediv c
  | _, c, ⟨d, rfl⟩ =>
    if cz : c = 0 then by simp [cz, Int.mul_zero] else by
      rw [Int.mul_left_comm, Int.mul_ediv_cancel_left _ cz, Int.mul_ediv_cancel_left _ cz]

protected theorem mul_div_assoc' (b : Int) {a c : Int} (h : c ∣ a) : a * b / c = a / c * b := by
  rw [Int.mul_comm, Int.mul_div_assoc _ h, Int.mul_comm]

protected theorem mul_ediv_assoc' (b : Int) {a c : Int}
    (h : c ∣ a) : (a * b).ediv c = a.ediv c * b := by
  rw [Int.mul_comm, Int.mul_ediv_assoc _ h, Int.mul_comm]

theorem div_dvd_div : ∀ {a b c : Int}, a ∣ b → b ∣ c → b / a ∣ c / a
  | a, _, _, ⟨b, rfl⟩, ⟨c, rfl⟩ => if az : a = 0 then by simp [az] else by
    rw [Int.mul_div_cancel_left _ az, Int.mul_assoc, Int.mul_div_cancel_left _ az]
    apply Int.dvd_mul_right

protected theorem eq_mul_of_div_eq_right {a b c : Int}
    (H1 : b ∣ a) (H2 : a / b = c) : a = b * c := by rw [← H2, Int.mul_div_cancel' H1]

protected theorem eq_mul_of_ediv_eq_right {a b c : Int}
    (H1 : b ∣ a) (H2 : a.ediv b = c) : a = b * c := by rw [← H2, Int.mul_ediv_cancel' H1]

protected theorem div_eq_of_eq_mul_right {a b c : Int}
    (H1 : b ≠ 0) (H2 : a = b * c) : a / b = c := by rw [H2, Int.mul_div_cancel_left _ H1]

protected theorem ediv_eq_of_eq_mul_right {a b c : Int}
    (H1 : b ≠ 0) (H2 : a = b * c) : a.ediv b = c := by rw [H2, Int.mul_ediv_cancel_left _ H1]

protected theorem eq_div_of_mul_eq_right {a b c : Int}
    (H1 : a ≠ 0) (H2 : a * b = c) : b = c / a :=
  (Int.div_eq_of_eq_mul_right H1 H2.symm).symm

protected theorem eq_ediv_of_mul_eq_right {a b c : Int}
    (H1 : a ≠ 0) (H2 : a * b = c) : b = c.ediv a :=
  (Int.ediv_eq_of_eq_mul_right H1 H2.symm).symm

protected theorem div_eq_iff_eq_mul_right {a b c : Int}
    (H : b ≠ 0) (H' : b ∣ a) : a / b = c ↔ a = b * c :=
  ⟨Int.eq_mul_of_div_eq_right H', Int.div_eq_of_eq_mul_right H⟩

protected theorem ediv_eq_iff_eq_mul_right {a b c : Int}
    (H : b ≠ 0) (H' : b ∣ a) : a.ediv b = c ↔ a = b * c :=
  ⟨Int.eq_mul_of_ediv_eq_right H', Int.ediv_eq_of_eq_mul_right H⟩

protected theorem div_eq_iff_eq_mul_left {a b c : Int}
    (H : b ≠ 0) (H' : b ∣ a) : a / b = c ↔ a = c * b := by
  rw [Int.mul_comm] <;> exact Int.div_eq_iff_eq_mul_right H H'

protected theorem ediv_eq_iff_eq_mul_left {a b c : Int}
    (H : b ≠ 0) (H' : b ∣ a) : a.ediv b = c ↔ a = c * b := by
  rw [Int.mul_comm] <;> exact Int.ediv_eq_iff_eq_mul_right H H'

protected theorem eq_mul_of_div_eq_left {a b c : Int}
    (H1 : b ∣ a) (H2 : a / b = c) : a = c * b := by
  rw [Int.mul_comm, Int.eq_mul_of_div_eq_right H1 H2]

protected theorem eq_mul_of_ediv_eq_left {a b c : Int}
    (H1 : b ∣ a) (H2 : a.ediv b = c) : a = c * b := by
  rw [Int.mul_comm, Int.eq_mul_of_ediv_eq_right H1 H2]

protected theorem div_eq_of_eq_mul_left {a b c : Int}
    (H1 : b ≠ 0) (H2 : a = c * b) : a / b = c :=
  Int.div_eq_of_eq_mul_right H1 (by rw [Int.mul_comm, H2])

protected theorem ediv_eq_of_eq_mul_left {a b c : Int}
    (H1 : b ≠ 0) (H2 : a = c * b) : a.ediv b = c :=
  Int.ediv_eq_of_eq_mul_right H1 (by rw [Int.mul_comm, H2])

protected theorem eq_zero_of_div_eq_zero {d n : Int} (h : d ∣ n) (H : n / d = 0) : n = 0 := by
  rw [← Int.mul_div_cancel' h, H, Int.mul_zero]

protected theorem eq_zero_of_ediv_eq_zero {d n : Int} (h : d ∣ n) (H : n.ediv d = 0) : n = 0 := by
  rw [← Int.mul_ediv_cancel' h, H, Int.mul_zero]

theorem neg_ediv_of_dvd : ∀ {a b : Int}, b ∣ a → (-a).ediv b = -(a.ediv b)
  | _, b, ⟨c, rfl⟩ => if bz : b = 0 then by simp [bz] else by
      rw [Int.neg_mul_eq_mul_neg, Int.mul_ediv_cancel_left _ bz, Int.mul_ediv_cancel_left _ bz]

theorem sub_ediv_of_dvd (a : Int) {b c : Int}
    (hcb : c ∣ b) : (a - b).ediv c = a.ediv c - b.ediv c := by
  rw [Int.sub_eq_add_neg, Int.sub_eq_add_neg, Int.add_ediv_of_dvd_right (Int.dvd_neg.2 hcb)]
  congr; exact Int.neg_ediv_of_dvd hcb

theorem sub_ediv_of_dvd_sub {a b c : Int}
    (hcab : c ∣ a - b) : (a - b).ediv c = a.ediv c - b.ediv c := by
  rw [← Int.add_sub_cancel ((a-b).ediv c), ← Int.add_ediv_of_dvd_left hcab, Int.sub_add_cancel]

@[simp] protected theorem div_left_inj {a b d : Int}
    (hda : d ∣ a) (hdb : d ∣ b) : a / d = b / d ↔ a = b := by
  refine ⟨fun h => ?_, congrArg (· / d)⟩
  rw [← Int.mul_div_cancel' hda, ← Int.mul_div_cancel' hdb, h]

@[simp] protected theorem ediv_left_inj {a b d : Int}
    (hda : d ∣ a) (hdb : d ∣ b) : a.ediv d = b.ediv d ↔ a = b := by
  refine ⟨fun h => ?_, congrArg (ediv · d)⟩
  rw [← Int.mul_ediv_cancel' hda, ← Int.mul_ediv_cancel' hdb, h]

theorem div_sign : ∀ a b, a / sign b = a * sign b
  | _, succ _ => by simp [sign, Int.mul_one]
  | _, 0 => by simp [sign, Int.mul_zero]
  | _, -[_+1] => by simp [sign, Int.mul_neg, Int.mul_one]

theorem ediv_sign : ∀ a b, a.ediv (sign b) = a * sign b
  | _, succ _ => by simp [sign, Int.mul_one]
  | _, 0 => by simp [sign, Int.mul_zero]
  | _, -[_+1] => by simp [sign, Int.mul_neg, Int.mul_one]

protected theorem sign_eq_div_abs (a : Int) : sign a = a / natAbs a :=
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

/- TODO

/-! ### `/` and ordering -/

protected theorem ediv_mul_le (a : Int) {b : Int} (H : b ≠ 0) : a.ediv b * b ≤ a :=
  Int.le_of_sub_nonneg <| by rw [Int.mul_comm, ← emod_def]; apply emod_nonneg _ H

protected theorem ediv_le_of_le_mul {a b c : Int} (H : 0 < c) (H' : a ≤ b * c) : a / c ≤ b :=
  le_of_mul_le_mul_right (le_trans (Int.div_mul_le _ (ne_of_gt H)) H') H

protected theorem mul_lt_of_lt_div {a b c : Int} (H : 0 < c) (H3 : a < b / c) : a * c < b :=
  lt_of_not_ge <| mt (Int.div_le_of_le_mul H) (not_le_of_gt H3)

protected theorem mul_le_of_le_div {a b c : Int} (H1 : 0 < c) (H2 : a ≤ b / c) : a * c ≤ b :=
  le_trans (Decidable.mul_le_mul_of_nonneg_right H2 (le_of_lt H1)) (Int.div_mul_le _ (ne_of_gt H1))

protected theorem le_div_of_mul_le {a b c : Int} (H1 : 0 < c) (H2 : a * c ≤ b) : a ≤ b / c :=
  le_of_lt_add_one <| lt_of_mul_lt_mul_right (lt_of_le_of_lt H2 (lt_div_add_one_mul_self _ H1)) (le_of_lt H1)

protected theorem le_div_iff_mul_le {a b c : Int} (H : 0 < c) : a ≤ b / c ↔ a * c ≤ b :=
  ⟨Int.mul_le_of_le_div H, Int.le_div_of_mul_le H⟩

protected theorem div_le_div {a b c : Int} (H : 0 < c) (H' : a ≤ b) : a / c ≤ b / c :=
  Int.le_div_of_mul_le H (le_trans (Int.div_mul_le _ (ne_of_gt H)) H')

protected theorem div_lt_of_lt_mul {a b c : Int} (H : 0 < c) (H' : a < b * c) : a / c < b :=
  lt_of_not_ge <| mt (Int.mul_le_of_le_div H) (not_le_of_gt H')

protected theorem lt_mul_of_div_lt {a b c : Int} (H1 : 0 < c) (H2 : a / c < b) : a < b * c :=
  lt_of_not_ge <| mt (Int.le_div_of_mul_le H1) (not_le_of_gt H2)

protected theorem div_lt_iff_lt_mul {a b c : Int} (H : 0 < c) : a / c < b ↔ a < b * c :=
  ⟨Int.lt_mul_of_div_lt H, Int.div_lt_of_lt_mul H⟩

protected theorem le_mul_of_div_le {a b c : Int} (H1 : 0 ≤ b) (H2 : b ∣ a) (H3 : a / b ≤ c) : a ≤ c * b := by
  rw [← Int.div_mul_cancel H2] <;> exact Decidable.mul_le_mul_of_nonneg_right H3 H1

protected theorem lt_div_of_mul_lt {a b c : Int} (H1 : 0 ≤ b) (H2 : b ∣ c) (H3 : a * b < c) : a < c / b :=
  lt_of_not_ge <| mt (Int.le_mul_of_div_le H1 H2) (not_le_of_gt H3)

protected theorem lt_div_iff_mul_lt {a b : Int} (c : Int) (H : 0 < c) (H' : c ∣ b) : a < b / c ↔ a * c < b :=
  ⟨Int.mul_lt_of_lt_div H, Int.lt_div_of_mul_lt (le_of_lt H) H'⟩

theorem div_pos_of_pos_of_dvd {a b : Int} (H1 : 0 < a) (H2 : 0 ≤ b) (H3 : b ∣ a) : 0 < a / b :=
  Int.lt_div_of_mul_lt H2 H3
    (by
      rwa [zero_mul])

theorem div_eq_div_of_mul_eq_mul {a b c d : Int} (H2 : d ∣ c) (H3 : b ≠ 0) (H4 : d ≠ 0) (H5 : a * d = b * c) :
    a / b = c / d :=
  Int.div_eq_of_eq_mul_right H3 <| by
    rw [← Int.mul_div_assoc _ H2] <;> exact (Int.div_eq_of_eq_mul_left H4 H5.symm).symm

theorem eq_mul_div_of_mul_eq_mul_of_dvd_left {a b c d : Int} (hb : b ≠ 0) (hbc : b ∣ c) (h : b * a = c * d) :
    a = c / b * d := by
  cases' hbc with k hk
  subst hk
  rw [Int.mul_div_cancel_left _ hb]
  rw [mul_assoc] at h
  apply mul_left_cancel₀ hb h

/-- If an integer with larger absolute value divides an integer, it is
zero. -/
theorem eq_zero_of_dvd_ofNatAbs_lt_natAbs {a b : Int} (w : a ∣ b) (h : natAbs b < natAbs a) : b = 0 := by
  rw [← natAbs_dvd, ← dvd_natAbs, ofNat_dvd] at w
  rw [← natAbs_eq_zero]
  exact eq_zero_of_dvd_of_lt w h

theorem eq_zero_of_dvd_of_nonneg_of_lt {a b : Int} (w₁ : 0 ≤ a) (w₂ : a < b) (h : b ∣ a) : a = 0 :=
  eq_zero_of_dvd_ofNatAbs_lt_natAbs h (natAbs_lt_natAbs_of_nonneg_of_lt w₁ w₂)

/-- If two integers are congruent to a sufficiently large modulus,
they are equal. -/
theorem eq_of_mod_eq_ofNatAbs_sub_lt_natAbs {a b c : Int} (h1 : a % b = c) (h2 : natAbs (a - c) < natAbs b) : a = c :=
  eq_of_sub_eq_zero (eq_zero_of_dvd_ofNatAbs_lt_natAbs (dvd_sub_of_mod_eq h1) h2)

theorem ofNat_add_negSucc_of_lt {m n : Nat} (h : m < n.succ) : ofNat m + -[n+1] = -[n+1 - m] := by
  change subNatNat _ _ = _
  have h' : n.succ - m = (n - m).succ
  apply succ_sub
  apply le_of_lt_succ h
  simp [*, subNatNat]

theorem ofNat_add_negSucc_of_ge {m n : Nat} (h : n.succ ≤ m) : ofNat m + -[n+1] = ofNat (m - n.succ) := by
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

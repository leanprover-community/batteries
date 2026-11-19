/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad, Mario Carneiro
-/
module

public import Batteries.Data.Nat.Basic

public section

/-! # Basic lemmas about natural numbers

The primary purpose of the lemmas in this file is to assist with reasoning
about sizes of objects, array indices and such. For a more thorough development
of the theory of natural numbers, we recommend using Mathlib.
-/

namespace Nat

/-! ### rec/cases -/

@[simp] theorem recAux_zero {motive : Nat → Sort _} (zero : motive 0)
    (succ : ∀ n, motive n → motive (n+1)) :
    Nat.recAux zero succ 0 = zero := rfl

theorem recAux_succ {motive : Nat → Sort _} (zero : motive 0)
    (succ : ∀ n, motive n → motive (n+1)) (n) :
    Nat.recAux zero succ (n+1) = succ n (Nat.recAux zero succ n) := rfl

@[simp] theorem recAuxOn_zero {motive : Nat → Sort _} (zero : motive 0)
    (succ : ∀ n, motive n → motive (n+1)) :
    Nat.recAuxOn 0 zero succ = zero := rfl

theorem recAuxOn_succ {motive : Nat → Sort _} (zero : motive 0)
    (succ : ∀ n, motive n → motive (n+1)) (n) :
    Nat.recAuxOn (n+1) zero succ = succ n (Nat.recAuxOn n zero succ) := rfl

@[simp] theorem casesAuxOn_zero {motive : Nat → Sort _} (zero : motive 0)
    (succ : ∀ n, motive (n+1)) :
    Nat.casesAuxOn 0 zero succ = zero := rfl

theorem casesAuxOn_succ {motive : Nat → Sort _} (zero : motive 0)
    (succ : ∀ n, motive (n+1)) (n) :
    Nat.casesAuxOn (n+1) zero succ = succ n := rfl

theorem strongRec_eq {motive : Nat → Sort _} (ind : ∀ n, (∀ m, m < n → motive m) → motive n)
    (t : Nat) : Nat.strongRec ind t = ind t fun m _ => Nat.strongRec ind m := by
  conv => lhs; unfold Nat.strongRec

theorem strongRecOn_eq {motive : Nat → Sort _} (ind : ∀ n, (∀ m, m < n → motive m) → motive n)
    (t : Nat) : Nat.strongRecOn t ind = ind t fun m _ => Nat.strongRecOn m ind :=
  WellFounded.fix_eq WellFoundedRelation.wf ind t

@[simp] theorem recDiagAux_zero_left {motive : Nat → Nat → Sort _}
    (zero_left : ∀ n, motive 0 n) (zero_right : ∀ m, motive m 0)
    (succ_succ : ∀ m n, motive m n → motive (m+1) (n+1)) (n) :
    Nat.recDiagAux zero_left zero_right succ_succ 0 n = zero_left n := by cases n <;> rfl

@[simp] theorem recDiagAux_zero_right {motive : Nat → Nat → Sort _}
    (zero_left : ∀ n, motive 0 n) (zero_right : ∀ m, motive m 0)
    (succ_succ : ∀ m n, motive m n → motive (m+1) (n+1)) (m)
    (h : zero_left 0 = zero_right 0 := by first | assumption | trivial) :
    Nat.recDiagAux zero_left zero_right succ_succ m 0 = zero_right m := by cases m; exact h; rfl

theorem recDiagAux_succ_succ {motive : Nat → Nat → Sort _}
    (zero_left : ∀ n, motive 0 n) (zero_right : ∀ m, motive m 0)
    (succ_succ : ∀ m n, motive m n → motive (m+1) (n+1)) (m n) :
    Nat.recDiagAux zero_left zero_right succ_succ (m+1) (n+1)
      = succ_succ m n (Nat.recDiagAux zero_left zero_right succ_succ m n) := rfl

@[simp] theorem recDiag_zero_zero {motive : Nat → Nat → Sort _} (zero_zero : motive 0 0)
    (zero_succ : ∀ n, motive 0 n → motive 0 (n+1)) (succ_zero : ∀ m, motive m 0 → motive (m+1) 0)
    (succ_succ : ∀ m n, motive m n → motive (m+1) (n+1)) :
    Nat.recDiag (motive:=motive) zero_zero zero_succ succ_zero succ_succ 0 0 = zero_zero := rfl

theorem recDiag_zero_succ {motive : Nat → Nat → Sort _} (zero_zero : motive 0 0)
    (zero_succ : ∀ n, motive 0 n → motive 0 (n+1)) (succ_zero : ∀ m, motive m 0 → motive (m+1) 0)
    (succ_succ : ∀ m n, motive m n → motive (m+1) (n+1)) (n) :
    Nat.recDiag zero_zero zero_succ succ_zero succ_succ 0 (n+1)
      = zero_succ n (Nat.recDiag zero_zero zero_succ succ_zero succ_succ 0 n) := by
  simp [Nat.recDiag]; rfl

theorem recDiag_succ_zero {motive : Nat → Nat → Sort _} (zero_zero : motive 0 0)
    (zero_succ : ∀ n, motive 0 n → motive 0 (n+1)) (succ_zero : ∀ m, motive m 0 → motive (m+1) 0)
    (succ_succ : ∀ m n, motive m n → motive (m+1) (n+1)) (m) :
    Nat.recDiag zero_zero zero_succ succ_zero succ_succ (m+1) 0
      = succ_zero m (Nat.recDiag zero_zero zero_succ succ_zero succ_succ m 0) := by
  simp [Nat.recDiag]; cases m <;> rfl

theorem recDiag_succ_succ {motive : Nat → Nat → Sort _} (zero_zero : motive 0 0)
    (zero_succ : ∀ n, motive 0 n → motive 0 (n+1)) (succ_zero : ∀ m, motive m 0 → motive (m+1) 0)
    (succ_succ : ∀ m n, motive m n → motive (m+1) (n+1)) (m n) :
    Nat.recDiag zero_zero zero_succ succ_zero succ_succ (m+1) (n+1)
      = succ_succ m n (Nat.recDiag zero_zero zero_succ succ_zero succ_succ m n) := rfl

@[simp] theorem recDiagOn_zero_zero {motive : Nat → Nat → Sort _} (zero_zero : motive 0 0)
    (zero_succ : ∀ n, motive 0 n → motive 0 (n+1)) (succ_zero : ∀ m, motive m 0 → motive (m+1) 0)
    (succ_succ : ∀ m n, motive m n → motive (m+1) (n+1)) :
    Nat.recDiagOn (motive:=motive) 0 0 zero_zero zero_succ succ_zero succ_succ = zero_zero := rfl

theorem recDiagOn_zero_succ {motive : Nat → Nat → Sort _} (zero_zero : motive 0 0)
    (zero_succ : ∀ n, motive 0 n → motive 0 (n+1)) (succ_zero : ∀ m, motive m 0 → motive (m+1) 0)
    (succ_succ : ∀ m n, motive m n → motive (m+1) (n+1)) (n) :
    Nat.recDiagOn 0 (n+1) zero_zero zero_succ succ_zero succ_succ
      = zero_succ n (Nat.recDiagOn 0 n zero_zero zero_succ succ_zero succ_succ) :=
  Nat.recDiag_zero_succ ..

theorem recDiagOn_succ_zero {motive : Nat → Nat → Sort _} (zero_zero : motive 0 0)
    (zero_succ : ∀ n, motive 0 n → motive 0 (n+1)) (succ_zero : ∀ m, motive m 0 → motive (m+1) 0)
    (succ_succ : ∀ m n, motive m n → motive (m+1) (n+1)) (m) :
    Nat.recDiagOn (m+1) 0 zero_zero zero_succ succ_zero succ_succ
      = succ_zero m (Nat.recDiagOn m 0 zero_zero zero_succ succ_zero succ_succ) :=
  Nat.recDiag_succ_zero ..

theorem recDiagOn_succ_succ {motive : Nat → Nat → Sort _} (zero_zero : motive 0 0)
    (zero_succ : ∀ n, motive 0 n → motive 0 (n+1)) (succ_zero : ∀ m, motive m 0 → motive (m+1) 0)
    (succ_succ : ∀ m n, motive m n → motive (m+1) (n+1)) (m n) :
    Nat.recDiagOn (m+1) (n+1) zero_zero zero_succ succ_zero succ_succ
      = succ_succ m n (Nat.recDiagOn m n zero_zero zero_succ succ_zero succ_succ) := rfl

@[simp] theorem casesDiagOn_zero_zero {motive : Nat → Nat → Sort _} (zero_zero : motive 0 0)
    (zero_succ : ∀ n, motive 0 (n+1)) (succ_zero : ∀ m, motive (m+1) 0)
    (succ_succ : ∀ m n, motive (m+1) (n+1)) :
    Nat.casesDiagOn 0 0 (motive:=motive) zero_zero zero_succ succ_zero succ_succ = zero_zero := rfl

@[simp] theorem casesDiagOn_zero_succ {motive : Nat → Nat → Sort _} (zero_zero : motive 0 0)
    (zero_succ : ∀ n, motive 0 (n+1)) (succ_zero : ∀ m, motive (m+1) 0)
    (succ_succ : ∀ m n, motive (m+1) (n+1)) (n) :
    Nat.casesDiagOn 0 (n+1) zero_zero zero_succ succ_zero succ_succ = zero_succ n := rfl

@[simp] theorem casesDiagOn_succ_zero {motive : Nat → Nat → Sort _} (zero_zero : motive 0 0)
    (zero_succ : ∀ n, motive 0 (n+1)) (succ_zero : ∀ m, motive (m+1) 0)
    (succ_succ : ∀ m n, motive (m+1) (n+1)) (m) :
    Nat.casesDiagOn (m+1) 0 zero_zero zero_succ succ_zero succ_succ = succ_zero m := rfl

@[simp] theorem casesDiagOn_succ_succ {motive : Nat → Nat → Sort _} (zero_zero : motive 0 0)
    (zero_succ : ∀ n, motive 0 (n+1)) (succ_zero : ∀ m, motive (m+1) 0)
    (succ_succ : ∀ m n, motive (m+1) (n+1)) (m n) :
    Nat.casesDiagOn (m+1) (n+1) zero_zero zero_succ succ_zero succ_succ = succ_succ m n := rfl

/-! ## strong case -/

/-- Strong case analysis on `a < b ∨ b ≤ a` -/
protected def lt_sum_ge (a b : Nat) : a < b ⊕' b ≤ a :=
  if h : a < b then .inl h else .inr (Nat.not_lt.1 h)

/-- Strong case analysis on `a < b ∨ a = b ∨ b < a` -/
protected def sum_trichotomy (a b : Nat) : a < b ⊕' a = b ⊕' b < a :=
  match h : compare a b with
  | .lt => .inl (Nat.compare_eq_lt.1 h)
  | .eq => .inr (.inl (Nat.compare_eq_eq.1 h))
  | .gt => .inr (.inr (Nat.compare_eq_gt.1 h))

/-! ### div/mod -/

-- TODO mod_core_congr, mod_def

-- TODO div_core_congr, div_def

-- TODO cont_to_bool_mod_two

theorem div_le_div_of_lt {a b : Nat} (n : Nat) (h : a < b) : a / n ≤ b / n :=
  Nat.div_le_div_right (Nat.le_of_lt h)

theorem le_of_div_lt_div {n a b : Nat} (h : a / n < b / n) : a ≤ b :=
  Nat.le_of_lt <| lt_of_div_lt_div h

theorem mod_lt_mod_of_lt_of_div_eq {n a b : Nat} (h : a < b) (h0 : a / n = b / n) :
    a % n < b % n := Nat.lt_of_add_lt_add_left (h0 ▸ div_add_mod b n ▸ div_add_mod a n ▸ h)

theorem mod_le_mod_of_le_of_div_eq {n a b : Nat} (h : a ≤ b) (h0 : a / n = b / n) :
    a % n ≤ b % n := Nat.le_of_add_le_add_left (h0 ▸ div_add_mod b n ▸ div_add_mod a n ▸ h)

theorem lt_of_div_eq_of_mod_lt {n a b : Nat} (h0 : a / n = b / n) (h1 : a % n < b % n) : a < b :=
  div_add_mod a n ▸ div_add_mod b n ▸ h0 ▸ Nat.add_lt_add_left h1 _

theorem le_of_div_eq_of_mod_le {n a b : Nat} (h0 : a / n = b / n) (h1 : a % n ≤ b % n) : a ≤ b :=
  div_add_mod a n ▸ div_add_mod b n ▸ h0 ▸ Nat.add_le_add_left h1 _

theorem lt_div_mod_iff (n a b : Nat) :
    a < b ↔ a / n < b / n ∨ a / n = b / n ∧ a % n < b % n :=
  ⟨fun h => (Nat.lt_or_eq_of_le (Nat.div_le_div_of_lt n h)).imp_right <|
    Iff.mpr ∘ and_iff_left_of_imp <| mod_lt_mod_of_lt_of_div_eq h,
    (·.elim lt_of_div_lt_div <| And.elim lt_of_div_eq_of_mod_lt)⟩

theorem le_div_mod_iff (n a b : Nat) :
    a ≤ b ↔ a / n < b / n ∨ a / n = b / n ∧ a % n ≤ b % n :=
  ⟨fun h => (Nat.lt_or_eq_of_le (Nat.div_le_div_right h)).imp_right <|
      Iff.mpr ∘ and_iff_left_of_imp <| mod_le_mod_of_le_of_div_eq h,
    (·.elim le_of_div_lt_div <| And.elim le_of_div_eq_of_mod_le)⟩

/-! ### mkDivMod -/

theorem mkDivMod_def (i : Nat) {n} (j : Fin n) : mkDivMod i j = n * i + j := rfl

@[simp, grind =] theorem div_mkDivMod (i : Nat) {n} (j : Fin n) :
    mkDivMod i j / n = i := ((Nat.mul_add_div j.pos ..)).trans
  (Nat.add_eq_left.mpr <| Nat.div_eq_of_lt j.isLt)

@[simp, grind =] theorem mod_mkDivMod (i : Nat) {n} (j : Fin n) :
    mkDivMod i j % n = j := (Nat.mul_add_mod ..).trans (Nat.mod_eq_of_lt j.isLt)

open Fin.NatCast in
@[simp, grind =] theorem cast_mkDivMod (i : Nat) {n : Nat} (j : Fin n) :
    haveI : NeZero n := ⟨Nat.ne_zero_of_lt j.isLt⟩
    (mkDivMod i j : Fin n) = j := Fin.ext <| mod_mkDivMod ..

theorem mkDivMod_div_add_mod (k : Nat) {n} (j : Fin n) :
    mkDivMod (k / n) j + k % n = k + j :=
  (Nat.add_right_comm ..).trans <| congrArg (· + j.val) (Nat.div_add_mod ..)

theorem mkDivMod_div (k : Nat) {n} (j : Fin n) : mkDivMod (k / n) j = k + j - k % n :=
  Nat.eq_sub_of_add_eq (k.mkDivMod_div_add_mod j)

open Fin.NatCast in
@[simp, grind =] theorem mkDivMod_div_cast (k : Nat) {n : Nat} [NeZero n] :
    mkDivMod (k / n) (k : Fin n) = k := n.ext_div_mod (div_mkDivMod ..) (mod_mkDivMod ..)

theorem mul_le_mkDivMod (i : Nat) {n} (j : Fin n) : n * i ≤ mkDivMod i j := Nat.le_add_right ..

theorem mkDivMod_lt_mul_succ (i : Nat) {n} (j : Fin n) : mkDivMod i j < n * (i + 1) :=
  Nat.add_lt_add_left j.isLt _

theorem mkDivMod_lt_mul_of_lt {i m : Nat} {n} (h : i < m) (j : Fin n) : mkDivMod i j < m * n :=
  Nat.lt_of_lt_of_le (mkDivMod_lt_mul_succ ..) <| Nat.mul_comm m n ▸ Nat.mul_le_mul_left _ h

@[simp, grind =] theorem mkDivMod_inj {i₁ i₂ : Nat} {n} {j₁ j₂ : Fin n} :
    mkDivMod i₁ j₁ = mkDivMod i₂ j₂ ↔ i₁ = i₂ ∧ j₁ = j₂ := by
  simp [n.ext_div_mod_iff (mkDivMod i₁ j₁), Fin.ext_iff]

@[simp, grind =] theorem mkDivMod_lt_mkDivMod_iff {i₁ i₂ : Nat} {n} {j₁ j₂ : Fin n} :
    mkDivMod i₁ j₁ < mkDivMod i₂ j₂ ↔ i₁ < i₂ ∨ i₁ = i₂ ∧ j₁ < j₂ := by
  simp [n.lt_div_mod_iff (mkDivMod i₁ j₁), Fin.lt_def]

@[simp, grind =] theorem mkDivMod_le_mkDivMod_iff {i₁ i₂ : Nat} {n} {j₁ j₂ : Fin n} :
    mkDivMod i₁ j₁ ≤ mkDivMod i₂ j₂ ↔ i₁ < i₂ ∨ i₁ = i₂ ∧ j₁ ≤ j₂ := by
  simp [n.le_div_mod_iff (mkDivMod i₁ j₁), Fin.le_def]

/-! ### ofBits -/

@[simp] theorem ofBits_zero (f : Fin 0 → Bool) : ofBits f = 0 := rfl

theorem ofBits_succ (f : Fin (n+1) → Bool) : ofBits f = 2 * ofBits (f ∘ Fin.succ) + (f 0).toNat :=
  Fin.foldr_succ ..

theorem ofBits_lt_two_pow (f : Fin n → Bool) : ofBits f < 2 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc ofBits f
        = 2 * ofBits (f ∘ Fin.succ) + (f 0).toNat := ofBits_succ ..
      _ < 2 * (ofBits (f ∘ Fin.succ) + 1) := Nat.add_lt_add_left (Bool.toNat_lt _) ..
      _ ≤ 2 * 2 ^ n := Nat.mul_le_mul_left 2 (ih ..)
      _ = 2 ^ (n + 1) := Nat.pow_add_one' .. |>.symm

@[simp] theorem testBit_ofBits_lt (f : Fin n → Bool) (i : Nat) (h : i < n) :
    (ofBits f).testBit i = f ⟨i, h⟩ := by
  induction n generalizing i with
  | zero => contradiction
  | succ n ih =>
    simp only [ofBits_succ]
    match i with
    | 0 => simp [mod_eq_of_lt (Bool.toNat_lt _)]
    | i+1 =>
      rw [testBit_add_one, mul_add_div Nat.zero_lt_two, Nat.div_eq_of_lt (Bool.toNat_lt _)]
      exact ih (f ∘ Fin.succ) i (Nat.lt_of_succ_lt_succ h)

@[simp] theorem testBit_ofBits_ge (f : Fin n → Bool) (i : Nat) (h : n ≤ i) :
    (ofBits f).testBit i = false := by
  apply testBit_lt_two_pow
  apply Nat.lt_of_lt_of_le
  · exact ofBits_lt_two_pow f
  · exact Nat.pow_le_pow_right Nat.zero_lt_two h

theorem testBit_ofBits (f : Fin n → Bool) :
    (ofBits f).testBit i = if h : i < n then f ⟨i, h⟩ else false := by
  cases Nat.lt_or_ge i n with
  | inl h => simp [h]
  | inr h => simp [h, Nat.not_lt_of_ge h]

theorem ofBits_testBit (x n) : ofBits (fun i : Fin n => x.testBit i) = x % 2 ^ n := by
  apply eq_of_testBit_eq; simp [testBit_ofBits]

/-! ### toString -/

private theorem toDigits_append_toDigits_pow_length
    (a b : Nat) (ha : a ≠ 0) :
    Nat.toDigits 10 a ++ Nat.toDigits 10 b =
      Nat.toDigits 10
        (a * 10 ^ (Nat.toDigits 10 b).length + b) := by
  induction b using Nat.base_induction 10 (by decide) with
  | single b hb =>
    simpa [Nat.toDigits_of_lt_base hb, Nat.mul_comm] using
      Nat.toDigits_append_toDigits (by decide) (Nat.pos_of_ne_zero ha) hb
  | digit m k hk hm ih =>
    have hmk := Nat.toDigits_append_toDigits (by decide) hm hk
    rw [← hmk, List.length_append, ← List.append_assoc, ih,
      Nat.toDigits_append_toDigits (by decide) (Nat.add_pos_right _ hm) hk]
    simp [Nat.toDigits_of_lt_base hk, Nat.pow_succ, Nat.mul_add]
    ac_rfl

theorem toString_append_toString (a b : Nat) (ha : a ≠ 0) :
    toString a ++ toString b = toString (a * 10 ^ (toString b).length + b) := by
  simpa only [Nat.toString_eq_ofList_toDigits, String.ofList_append, String.length_ofList] using
    congrArg String.ofList (toDigits_append_toDigits_pow_length a b ha)

/-! ### Misc -/

theorem mul_add_lt_mul_of_lt_of_lt {m n x y : Nat} (hx : x < m) (hy : y < n) :
    n * x + y < m * n := mkDivMod_lt_mul_of_lt hx ⟨y, hy⟩

theorem add_mul_lt_mul_of_lt_of_lt {m n x y : Nat} (hx : x < m) (hy : y < n) :
    x + m * y < m * n := by
  rw [Nat.add_comm, Nat.mul_comm _ n]
  exact mul_add_lt_mul_of_lt_of_lt hy hx

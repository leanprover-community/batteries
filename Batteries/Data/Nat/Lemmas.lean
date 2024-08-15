/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad, Mario Carneiro
-/
import Batteries.Tactic.Alias
import Batteries.Data.Nat.Basic

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
  Nat.strongRec_eq ..

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

/-! ## add -/

@[deprecated (since := "2023-11-25")] alias succ_add_eq_succ_add := Nat.succ_add_eq_add_succ

/-! ## sub -/

@[deprecated (since := "2023-11-25")]
protected alias le_of_le_of_sub_le_sub_right := Nat.le_of_sub_le_sub_right

@[deprecated (since := "2023-11-25")]
protected alias le_of_le_of_sub_le_sub_left := Nat.le_of_sub_le_sub_left

/-! ### mul -/

@[deprecated (since := "2024-01-11")] protected alias mul_lt_mul := Nat.mul_lt_mul_of_lt_of_le'

@[deprecated (since := "2024-01-11")] protected alias mul_lt_mul' := Nat.mul_lt_mul_of_le_of_lt

/-! ### div/mod -/

-- TODO mod_core_congr, mod_def

-- TODO div_core_congr, div_def

-- TODO cont_to_bool_mod_two

/-! ### sum -/

@[simp] theorem sum_append : Nat.sum (l₁ ++ l₂) = Nat.sum l₁ + Nat.sum l₂ := by
  induction l₁ <;> simp [*, Nat.add_assoc]

@[deprecated (since := "2024-03-05")] protected alias lt_connex := Nat.lt_or_gt_of_ne
@[deprecated (since := "2024-02-09")] alias pow_two_pos := Nat.two_pow_pos

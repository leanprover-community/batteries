/-
Copyright (c) 2022 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Batteries.Data.Fin.Basic
import Batteries.Data.List.Lemmas
import Batteries.Tactic.Lint.Simp

namespace Fin

attribute [norm_cast] val_last

@[nolint simpNF, simp]
theorem val_ndrec (x : Fin n) (h : m = n) : (h ▸ x).val = x.val := by
  cases h; rfl

/-! ### clamp -/

@[simp] theorem coe_clamp (n m : Nat) : (clamp n m : Nat) = min n m := rfl

/-! ### foldr -/

theorem map_foldr {g : α → β} {f : Fin n → α → α} {f' : Fin n → β → β}
    (h : ∀ i x, g (f i x) = f' i (g x)) (x) : g (foldr n f x) = foldr n f' (g x) := by
  induction n generalizing x with
  | zero => simp
  | succ n ih => simp [foldr_succ, ih, h]

/-! ### sum -/

@[simp] theorem sum_zero [OfNat α (nat_lit 0)] [Add α] (x : Fin 0 → α) :
    Fin.sum x = 0 := by
  simp [Fin.sum]

theorem sum_succ [OfNat α (nat_lit 0)] [Add α] (x : Fin (n + 1) → α) :
    Fin.sum x = x 0 + Fin.sum (x ∘ Fin.succ) := by
  simp [Fin.sum, foldr_succ]

/-! ### prod -/

@[simp] theorem prod_zero [OfNat α (nat_lit 1)] [Mul α] (x : Fin 0 → α) :
    Fin.prod x = 1 := by
  simp [Fin.prod]

theorem prod_succ [OfNat α (nat_lit 1)] [Mul α] (x : Fin (n + 1) → α) :
    Fin.prod x = x 0 * Fin.prod (x ∘ Fin.succ) := by
  simp [Fin.prod, foldr_succ]

/-! ### count -/

@[simp] theorem count_zero (P : Fin 0 → Prop) [DecidablePred P] : Fin.count P = 0 := by
  simp [Fin.count]

theorem count_succ (P : Fin (n + 1) → Prop) [DecidablePred P] : Fin.count P =
    if P 0 then Fin.count (fun i => P i.succ) + 1 else Fin.count (fun i => P i.succ) := by
  split <;> simp [Fin.count, Fin.sum_succ, Nat.one_add, Function.comp_def, *]

theorem count_le (P : Fin n → Prop) [DecidablePred P] : Fin.count P ≤ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [count_succ]
    split
    · simp [ih]
    · apply Nat.le_trans _ (Nat.le_succ n); simp [ih]

/-! ### find? -/

@[simp] theorem find?_zero {P : Fin 0 → Prop} [DecidablePred P] : Fin.find? P = none := by
  simp [Fin.find?]

theorem find?_succ (P : Fin (n+1) → Prop) [DecidablePred P] :
    Fin.find? P = if P 0 then some 0 else (Fin.find? fun i => P i.succ).map Fin.succ := by
  have h (i : Fin n) (v : Option (Fin n)) :
      (if P i.succ then some i else v).map Fin.succ =
        if P i.succ then some i.succ else v.map Fin.succ := by
    intros; split <;> simp
  simp [Fin.find?, foldr_succ, map_foldr h]

theorem find?_prop {P : Fin n → Prop} [DecidablePred P] (h : Fin.find? P = some x) : P x := by
  induction n with
  | zero => simp at h
  | succ n ih =>
    simp [find?_succ] at h
    split at h
    · cases h; assumption
    · simp [Option.map_eq_some] at h
      match h with
      | ⟨i, h', hi⟩ => cases hi; exact ih h'

theorem find?_isSome_of_prop {P : Fin n → Prop} [DecidablePred P] (h : P x) :
    (Fin.find? P).isSome := by
  induction n with
  | zero => nomatch x
  | succ n ih =>
    rw [find?_succ]
    split
    · rfl
    · have hx : x ≠ 0 := by
        intro hx
        rw [hx] at h
        contradiction
      have h : P (x.pred hx).succ := by simp [h]
      rw [Option.isSome_map']
      exact ih h

theorem find?_isSome_iff_exists {P : Fin n → Prop} [DecidablePred P] :
    (Fin.find? P).isSome ↔ ∃ x, P x := by
  constructor
  · intro h
    match heq : Fin.find? P with
    | some x => exists x; exact find?_prop heq
    | none => rw [heq] at h; contradiction
  · intro ⟨_, h⟩
    exact find?_isSome_of_prop h

/-! ### recZeroSuccOn -/

unseal Fin.recZeroSuccOn in
@[simp] theorem recZeroSuccOn_zero {motive : Fin (n+1) → Sort _} (zero : motive 0)
    (succ : (x : Fin n) → motive x.castSucc → motive x.succ) :
    Fin.recZeroSuccOn 0 zero succ = zero := rfl

unseal Fin.recZeroSuccOn in
theorem recZeroSuccOn_succ {motive : Fin (n+1) → Sort _} (x : Fin n)  (zero : motive 0)
    (succ : (x : Fin n) → motive x.castSucc → motive x.succ) :
    Fin.recZeroSuccOn x.succ zero succ = succ x (Fin.recZeroSuccOn x.castSucc zero succ) := rfl

/-! ### casesZeroSuccOn -/

@[simp] theorem casesZeroSuccOn_zero {motive : Fin (n+1) → Sort _} (zero : motive 0)
    (succ : (x : Fin n) → motive x.succ) : Fin.casesZeroSuccOn 0 zero succ = zero := rfl

@[simp] theorem casesZeroSuccOn_succ {motive : Fin (n+1) → Sort _} (x : Fin n)  (zero : motive 0)
    (succ : (x : Fin n) → motive x.succ) : Fin.casesZeroSuccOn x.succ zero succ = succ x := rfl

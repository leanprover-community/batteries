/-
Copyright (c) 2022 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Batteries.Data.Fin.Basic
import Batteries.Data.List.Lemmas

namespace Fin

attribute [norm_cast] val_last

/-! ### clamp -/

@[simp] theorem coe_clamp (n m : Nat) : (clamp n m : Nat) = min n m := rfl

/-! ### Fin.findMap? -/

@[simp] theorem findMap?_zero (f : Fin 0 → Option α) : findMap? f = none := rfl

theorem findMap?_succ (f : Fin (n+1) → Option α) :
    findMap? f = (f 0 <|> findMap? fun i => f i.succ) := by
  simp only [findMap?, foldl_succ, Option.none_orElse, Function.comp_apply]
  cases f 0
  · rw [Option.none_orElse]
  · rw [Option.some_orElse]
    induction n with
    | zero => rfl
    | succ n ih => rw [foldl_succ, Option.some_orElse, ih fun i => f i.succ]

theorem exists_eq_some_of_findMap?_eq_some {f : Fin n → Option α} (h : findMap? f = some x) :
    ∃ i, f i = some x := by
  induction n with
  | zero => rw [findMap?_zero] at h; contradiction
  | succ n ih =>
    rw [findMap?_succ] at h
    match heq : f 0 with
    | some x =>
      rw [heq, Option.some_orElse] at h
      exists 0
      rw [heq, h]
    | none =>
      rw [heq, Option.none_orElse] at h
      match ih h with | ⟨i, _⟩ => exists i.succ

theorem eq_none_of_findMap?_eq_none {f : Fin n → Option α} (h : findMap? f = none) (i) :
    f i = none := by
  induction n with
  | zero => cases i; contradiction
  | succ n ih =>
    rw [findMap?_succ] at h
    match heq : f 0 with
    | some x =>
      rw [heq, Option.some_orElse] at h
      contradiction
    | none =>
      rw [heq, Option.none_orElse] at h
      cases i using Fin.cases with
      | zero => exact heq
      | succ i => exact ih h i

@[simp] theorem findMap?_isSome {f : Fin n → Option α} :
    (findMap? f).isSome ↔ ∃ i, (f i).isSome := by
  simp only [Option.isSome_iff_exists]
  constructor
  · intro ⟨x, hx⟩
    match exists_eq_some_of_findMap?_eq_some hx with
    | ⟨i, hi⟩ => exists i, x
  · intro ⟨i, x, hix⟩
    match h : findMap? f with
    | some x => exists x
    | none => rw [eq_none_of_findMap?_eq_none h i] at hix; contradiction

@[simp] theorem findMap?_eq_none {f : Fin n → Option α} :
    findMap? f = none ↔ ∀ i, f i = none := by
  constructor
  · exact eq_none_of_findMap?_eq_none
  · intro hf
    match h : findMap? f with
    | none => rfl
    | some x =>
      match exists_eq_some_of_findMap?_eq_some h with
      | ⟨i, h⟩ => rw [hf] at h; contradiction

theorem findMap?_isNone {f : Fin n → Option α} : (findMap? f).isNone ↔ ∀ i, (f i).isNone := by simp

theorem map_findMap?_eq_findMap?_map (g : α → β) (f : Fin n → Option α) :
    (findMap? f).map g = findMap? fun i => (f i).map g := by
  induction n with
  | zero => rfl
  | succ n ih => simp [findMap?_succ, Option.map_orElse, ih]

theorem findMap?_eq_findMap?_finRange (f : Fin n → Option α) :
    findMap? f = (List.finRange n).findMap? f := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [findMap?_succ, List.finRange_succ, List.findMap?_cons]
    cases f 0 <;> simp [ih, List.findMap?_map]

/-! ### Fin.find? -/

@[simp] theorem find?_zero (p : Fin 0 → Bool) : find? p = none := rfl

theorem find?_succ (p : Fin (n+1) → Bool) :
    find? p = if p 0 then some 0 else (find? fun i => p i.succ).map Fin.succ := by
  simp [find?, findMap?_succ]
  split <;> simp [map_findMap?_eq_findMap?_map]


theorem eq_true_of_find?_eq_some {p : Fin n → Bool} (h : find? p = some i) : p i = true := by
  match exists_eq_some_of_findMap?_eq_some h with
  | ⟨i, hi⟩ =>
    split at hi
    · cases hi; assumption
    · contradiction

theorem eq_false_of_find?_eq_none {p : Fin n → Bool} (h : find? p = none) (i) : p i = false := by
  have hi := eq_none_of_findMap?_eq_none h i
  split at hi
  · contradiction
  · simp [*]

theorem find?_isSome {p : Fin n → Bool} : (find? p).isSome ↔ ∃ i, p i := by
  simp [find?, findMap?_isSome]

theorem find?_isNone {p : Fin n → Bool} : (find? p).isNone ↔ ∀ i, ¬ p i := by
  simp [find?, findMap?_isSome]

theorem find?_eq_find?_finRange {p : Fin n → Bool} : find? p = (List.finRange n).find? p := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [find?_succ, List.finRange_succ, List.find?_cons]
    split <;> simp [Function.comp_def, *]

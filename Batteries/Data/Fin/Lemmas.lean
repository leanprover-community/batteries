/-
Copyright (c) 2022 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Batteries.Data.Fin.Basic
import Batteries.Data.List.Lemmas
import Batteries.Util.ProofWanted

namespace Fin

attribute [norm_cast] val_last

/-! ### clamp -/

@[simp] theorem coe_clamp (n m : Nat) : (clamp n m : Nat) = min n m := rfl

/-! ### findSome? -/

@[simp] theorem findSome?_zero {f : Fin 0 → Option α} : findSome? f = none := rfl

@[simp] theorem findSome?_one {f : Fin 1 → Option α} : findSome? f = f 0 := rfl

theorem findSome?_succ {f : Fin (n+1) → Option α} :
    findSome? f = (f 0 <|> findSome? fun i => f i.succ) := by
  simp only [findSome?, foldl_succ, Option.none_orElse, Function.comp_apply]
  cases f 0
  · rw [Option.none_orElse]
  · rw [Option.some_orElse]
    induction n with
    | zero => rfl
    | succ n ih => rw [foldl_succ, Option.some_orElse, ih (f := fun i => f i.succ)]

theorem findSome?_succ_of_some {f : Fin (n+1) → Option α} (h : f 0 = some x) :
    findSome? f = some x := by simp [findSome?_succ, h]

theorem findSome?_succ_of_isSome {f : Fin (n+1) → Option α} (h : (f 0).isSome) :
    findSome? f = f 0 := by cases _h : f 0 <;> simp_all [findSome?_succ_of_some]

theorem findSome?_succ_of_none {f : Fin (n+1) → Option α} (h : f 0 = none) :
    findSome? f = findSome? fun i => f i.succ := by simp [findSome?_succ, h]

theorem findSome?_succ_of_isNone {f : Fin (n+1) → Option α} (h : (f 0).isNone) :
    findSome? f = findSome? fun i => f i.succ := by simp_all [findSome?_succ_of_none]

theorem exists_of_findSome?_eq_some {f : Fin n → Option α} (h : findSome? f = some x) :
    ∃ i, f i = some x := by
  induction n with
  | zero => rw [findSome?_zero] at h; contradiction
  | succ n ih =>
    rw [findSome?_succ] at h
    match heq : f 0 with
    | some x =>
      rw [heq, Option.some_orElse] at h
      exists 0
      rw [heq, h]
    | none =>
      rw [heq, Option.none_orElse] at h
      match ih h with | ⟨i, _⟩ => exists i.succ

theorem eq_none_of_findSome?_eq_none {f : Fin n → Option α} (h : findSome? f = none) (i) :
    f i = none := by
  induction n with
  | zero => cases i; contradiction
  | succ n ih =>
    rw [findSome?_succ] at h
    match heq : f 0 with
    | some x =>
      rw [heq, Option.some_orElse] at h
      contradiction
    | none =>
      rw [heq, Option.none_orElse] at h
      cases i using Fin.cases with
      | zero => exact heq
      | succ i => exact ih h i

@[simp] theorem findSome?_isSome_iff {f : Fin n → Option α} :
    (findSome? f).isSome ↔ ∃ i, (f i).isSome := by
  simp only [Option.isSome_iff_exists]
  constructor
  · intro ⟨x, hx⟩
    match exists_of_findSome?_eq_some hx with
    | ⟨i, hi⟩ => exists i, x
  · intro ⟨i, x, hix⟩
    match h : findSome? f with
    | some x => exists x
    | none => rw [eq_none_of_findSome?_eq_none h i] at hix; contradiction

@[simp] theorem findSome?_eq_none_iff {f : Fin n → Option α} :
    findSome? f = none ↔ ∀ i, f i = none := by
  constructor
  · exact eq_none_of_findSome?_eq_none
  · intro hf
    match h : findSome? f with
    | none => rfl
    | some x =>
      match exists_of_findSome?_eq_some h with
      | ⟨i, h⟩ => rw [hf] at h; contradiction

theorem findSome?_isNone_iff {f : Fin n → Option α} :
    (findSome? f).isNone ↔ ∀ i, (f i).isNone := by simp

theorem map_findSome? (f : Fin n → Option α) (g : α → β) :
    (findSome? f).map g = findSome? (Option.map g ∘ f) := by
  induction n with
  | zero => rfl
  | succ n ih => simp [findSome?_succ, Function.comp_def, Option.map_orElse, ih]

theorem findSome?_guard {p : Fin n → Bool} : findSome? (Option.guard fun i => p i) = find? p := rfl

theorem findSome?_eq_findSome?_finRange (f : Fin n → Option α) :
    findSome? f = (List.finRange n).findSome? f := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [findSome?_succ, List.finRange_succ, List.findSome?_cons]
    cases f 0 <;> simp [ih, List.findSome?_map, Function.comp_def]

/-! ### Fin.find? -/

@[simp] theorem find?_zero {p : Fin 0 → Bool} : find? p = none := rfl

@[simp] theorem find?_one {p : Fin 1 → Bool} : find? p = if p 0 then some 0 else none := rfl

theorem find?_succ {p : Fin (n+1) → Bool} :
    find? p = if p 0 then some 0 else (find? fun i => p i.succ).map Fin.succ := by
  simp only [find?, findSome?_succ, Option.guard]
  split <;> simp [Option.none_orElse, map_findSome?, Function.comp_def, Option.guard]

theorem eq_true_of_find?_eq_some {p : Fin n → Bool} (h : find? p = some i) : p i = true := by
  match exists_of_findSome?_eq_some h with
  | ⟨i, hi⟩ =>
    simp only [Option.guard] at hi
    split at hi
    · cases hi; assumption
    · contradiction

theorem eq_false_of_find?_eq_none {p : Fin n → Bool} (h : find? p = none) (i) : p i = false := by
  have hi := eq_none_of_findSome?_eq_none h i
  simp only [Option.guard] at hi
  split at hi
  · contradiction
  · simp [*]

theorem find?_isSome_iff {p : Fin n → Bool} : (find? p).isSome ↔ ∃ i, p i := by
  simp [find?, findSome?_isSome_iff]

theorem find?_isNone_iff {p : Fin n → Bool} : (find? p).isNone ↔ ∀ i, ¬ p i := by
  simp [find?, findSome?_isSome_iff]

proof_wanted find?_eq_some_iff {p : Fin n → Bool} : find? p = some i ↔ p i ∧ ∀ j, j < i → ¬ p j

theorem find?_eq_none_iff {p : Fin n → Bool} : find? p = none ↔ ∀ i, ¬ p i := by
  rw [← find?_isNone_iff, Option.isNone_iff_eq_none]

theorem find?_eq_find?_finRange {p : Fin n → Bool} : find? p = (List.finRange n).find? p := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [find?_succ, List.finRange_succ, List.find?_cons]
    split <;> simp [Function.comp_def, *]

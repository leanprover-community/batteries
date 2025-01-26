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

/-! ### Fin.find? -/

@[simp] theorem find?_zero (f : Fin 0 → Option α) : find? f = none := rfl

theorem find?_succ (f : Fin (n+1) → Option α) :
    find? f = (f 0 <|> find? (f ∘ Fin.succ)) := by
  simp only [find?, foldl_succ, Option.none_orElse, Function.comp_apply]
  cases f 0
  · rw [Option.none_orElse]
  · rw [Option.some_orElse]
    induction n with
    | zero => rfl
    | succ n ih =>
      have h := ih (f ∘ Fin.succ)
      simp only [Function.comp_apply] at h
      rw [foldl_succ, Option.some_orElse, h]

theorem exists_eq_some_of_find?_eq_some {f : Fin n → Option α} (h : find? f = some x) :
    ∃ i, f i = some x := by
  induction n with
  | zero => rw [find?_zero] at h; contradiction
  | succ n ih =>
    rw [find?_succ] at h
    match heq : f 0 with
    | some x =>
      rw [heq, Option.some_orElse] at h
      exists 0
      rw [heq, h]
    | none =>
      rw [heq, Option.none_orElse] at h
      match ih h with | ⟨i, _⟩ => exists i.succ

theorem eq_none_of_find?_eq_none {f : Fin n → Option α} (h : find? f = none) (i) : f i = none := by
  induction n with
  | zero => cases i; contradiction
  | succ n ih =>
    rw [find?_succ] at h
    match heq : f 0 with
    | some x =>
      rw [heq, Option.some_orElse] at h
      contradiction
    | none =>
      rw [heq, Option.none_orElse] at h
      cases i using Fin.cases with
      | zero => exact heq
      | succ i => exact ih h i

@[simp] theorem find?_isSome {f : Fin n → Option α} : (find? f).isSome ↔ ∃ i, (f i).isSome := by
  simp only [Option.isSome_iff_exists]
  constructor
  · intro ⟨x, hx⟩
    match exists_eq_some_of_find?_eq_some hx with
    | ⟨i, hi⟩ => exists i, x
  · intro ⟨i, x, hix⟩
    match h : find? f with
    | some x => exists x
    | none => rw [eq_none_of_find?_eq_none h i] at hix; contradiction

@[simp] theorem find?_eq_none {f : Fin n → Option α} : find? f = none ↔ ∀ i, f i = none := by
  constructor
  · exact eq_none_of_find?_eq_none
  · intro hf
    match h : find? f with
    | none => rfl
    | some x =>
      match exists_eq_some_of_find?_eq_some h with
      | ⟨i, h⟩ => rw [hf] at h; contradiction

theorem find?_isNone {f : Fin n → Option α} : (find? f).isNone ↔ ∀ i, (f i).isNone := by simp

theorem find?_eq_list_join_find?_ofFn_isSome {f : Fin n → Option α} :
    find? f = ((List.ofFn f).find? Option.isSome).join := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [find?_succ, List.ofFn_succ, List.find?_cons]
    match h : f 0 with
    | some x => simp
    | none => simp [ih, Function.comp_def]

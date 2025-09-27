/-
Copyright (c) 2022 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Batteries.Data.Fin.Basic
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
  simp only [findSome?, foldl_succ]
  cases f 0
  · rw [Option.orElse_eq_orElse, Option.orElse_none, Option.orElse_none]
  · simp only [Option.orElse_some, Option.orElse_eq_orElse, Option.orElse_none]
    induction n with
    | zero => rfl
    | succ n ih => rw [foldl_succ, Option.orElse_some, ih (f := fun i => f i.succ)]

theorem findSome?_succ_of_some {f : Fin (n+1) → Option α} (h : f 0 = some x) :
    findSome? f = some x := by simp [findSome?_succ, h]

theorem findSome?_succ_of_isSome {f : Fin (n+1) → Option α} (h : (f 0).isSome) :
    findSome? f = f 0 := by cases _h : f 0 <;> simp_all [findSome?_succ_of_some]

theorem findSome?_succ_of_none {f : Fin (n+1) → Option α} (h : f 0 = none) :
    findSome? f = findSome? fun i => f i.succ := by simp [findSome?_succ, h]

theorem findSome?_succ_of_isNone {f : Fin (n+1) → Option α} (h : (f 0).isNone) :
    findSome? f = findSome? fun i => f i.succ := by simp_all [findSome?_succ_of_none]

@[simp]
theorem findSome?_eq_some_iff {f : Fin n → Option α} :
    findSome? f = some a ↔ ∃ i, f i = some a ∧ ∀ j < i, f j = none := by
  induction n with
  | zero =>
    simp only [findSome?_zero, (Option.some_ne_none _).symm, false_iff]
    exact fun  ⟨i, _⟩ => i.elim0
  | succ n ih =>
    simp only [findSome?_succ, Option.orElse_eq_orElse, Option.orElse_eq_or, Option.or_eq_some_iff,
      ih, forall_fin_succ, exists_fin_succ, false_implies, not_lt_zero, implies_true,
      and_true, succ_pos, forall_const, succ_lt_succ_iff, and_left_comm (b := f 0 = none),
      exists_and_left]

@[simp]
theorem findSome?_isSome_iff {f : Fin n → Option α} :
    (findSome? f).isSome ↔ ∃ i, (f i).isSome ∧ ∀ j < i, (f j).isNone := by
  simp only [Option.isSome_iff_exists, findSome?_eq_some_iff, exists_comm, exists_and_right,
    Option.isNone_iff_eq_none]

@[simp] theorem findSome?_eq_none_iff {f : Fin n → Option α} :
    findSome? f = none ↔ ∀ i, f i = none := by
  induction n with
  | zero =>
    simp only [findSome?_zero, true_iff]
    exact fun i => i.elim0
  | succ n ih =>
    simp only [findSome?_succ, Option.orElse_eq_orElse,
      Option.orElse_eq_or, Option.or_eq_none_iff, ih, forall_fin_succ]

theorem findSome?_isNone_iff {f : Fin n → Option α} :
    (findSome? f).isNone ↔ ∀ i, (f i).isNone := by simp

theorem exists_of_findSome?_eq_some {f : Fin n → Option α} (h : findSome? f = some x) :
    ∃ i, f i = some x ∧ ∀ j < i, f j = none :=
  findSome?_eq_some_iff.1 h

theorem exists_of_findSome?_eq_some' {f : Fin n → Option α} (h : findSome? f = some x) :
    ∃ i, f i = some x := by
  rw [findSome?_eq_some_iff] at h
  grind

theorem eq_none_of_findSome?_eq_none {f : Fin n → Option α} (h : findSome? f = none) (i) :
    f i = none := findSome?_eq_none_iff.1 h i

theorem exists_of_findSome?_isSome {f : Fin n → Option α} (h : (findSome? f).isSome) :
    ∃ i, (f i).isSome ∧ ∀ j < i, (f j).isNone := by
  rwa [findSome?_isSome_iff] at h

theorem exists_of_findSome?_isSome' {f : Fin n → Option α} (h : (findSome? f).isSome) :
    ∃ i, (f i).isSome := by
  rw [findSome?_isSome_iff] at h
  grind

theorem isNone_of_findSome?_isNone {f : Fin n → Option α} (h : (findSome? f).isNone) :
    (f i).isNone := findSome?_isNone_iff.1 h i

theorem isSome_findSome?_of_isSome {f : Fin n → Option α} (h : (f i).isSome) :
    (findSome? f).isSome := by
  simp only [Option.isSome_iff_ne_none, ne_eq, findSome?_eq_none_iff]
  grind

theorem findSome?_isSome_iff' {f : Fin n → Option α} :
    (findSome? f).isSome ↔ ∃ i, (f i).isSome :=
  ⟨exists_of_findSome?_isSome', fun ⟨_, h⟩ => isSome_findSome?_of_isSome h⟩

theorem map_findSome? (f : Fin n → Option α) (g : α → β) :
    (findSome? f).map g = findSome? (Option.map g ∘ f) := by
  induction n with
  | zero => rfl
  | succ n ih => simp [findSome?_succ, Function.comp_def, Option.map_or, ih]

theorem findSome?_guard {p : Fin n → Bool} : findSome? (Option.guard p) = find? p := rfl

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
  split <;> simp [map_findSome?, Function.comp_def, Option.guard]

theorem find?_eq_some_iff {p : Fin n → Bool} :
    find? p = some i ↔ p i ∧ ∀ j, j < i → ¬ p j := by
  simp [find?, and_assoc]

theorem find?_isSome_iff {p : Fin n → Bool} :
    (find? p).isSome ↔ ∃ i, p i ∧ ∀ j < i, ¬ p j := by
  simp [find?]

theorem find?_eq_none_iff {p : Fin n → Bool} : find? p = none ↔ ∀ i, ¬ p i := by
  simp [find?]

theorem find?_isNone_iff {p : Fin n → Bool} : (find? p).isNone ↔ ∀ i, ¬ p i := by
  simp [find?]

theorem eq_true_of_find?_eq_some {p : Fin n → Bool} (h : find? p = some i) :
    p i ∧ ∀ j < i, ¬ p j := by
  rwa [find?_eq_some_iff] at h

theorem eq_false_of_find?_eq_none {p : Fin n → Bool} (h : find? p = none) (i) :
    ¬ p i := by
  rw [find?_eq_none_iff] at h
  grind

theorem exists_of_find?_isSome {p : Fin n → Bool} (h : (find? p).isSome) :
    ∃ i, p i ∧ ∀ j < i, ¬ p j := by
  rwa [find?_isSome_iff] at h

theorem exists_of_find?_isSome' {p : Fin n → Bool} (h : (find? p).isSome) :
    ∃ i, p i := by
  have H := exists_of_find?_isSome h
  grind

theorem isNone_of_find?_isNone  (h : (find? p).isNone) : ¬ p i := by
  simp only [Option.isNone_iff_eq_none, find?_eq_none_iff] at h ⊢
  exact h _

 theorem isSome_find?_of_isSome (h : p i) :
    (find? p).isSome := by
  simp only [Option.isSome_iff_ne_none, ne_eq, find?_eq_none_iff]
  grind

theorem find?_isSome_iff' {p : Fin n → Bool} : (find? p).isSome ↔ ∃ i, p i :=
  ⟨exists_of_find?_isSome', fun ⟨_, h⟩ => isSome_find?_of_isSome h⟩

theorem find?_eq_find?_finRange {p : Fin n → Bool} : find? p = (List.finRange n).find? p := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [find?_succ, List.finRange_succ, List.find?_cons]
    split <;> simp [Function.comp_def, *]

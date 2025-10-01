/-
Copyright (c) 2022 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Batteries.Data.Fin.Basic
public import Batteries.Util.ProofWanted
public import Batteries.Tactic.Alias

@[expose] public section

namespace Fin

attribute [norm_cast] val_last

/-! ### foldl/foldr -/

theorem foldl_assoc {op : α → α → α} [ha : Std.Associative op] {f : Fin n → α} {a₁ a₂} :
    foldl n (fun x i => op x (f i)) (op a₁ a₂) = op a₁ (foldl n (fun x i => op x (f i)) a₂) := by
  induction n generalizing a₂ with
  | zero => rfl
  | succ n ih => simp only [foldl_succ, ha.assoc, ih]

theorem foldr_assoc {op : α → α → α} [ha : Std.Associative op] {f : Fin n → α} {a₁ a₂} :
    foldr n (fun i x => op (f i) x) (op a₁ a₂) = op (foldr n (fun i x => op (f i) x) a₁) a₂ := by
  induction n generalizing a₂ with
  | zero => rfl
  | succ n ih => simp only [foldr_succ, ha.assoc, ih]

/-! ### clamp -/

@[simp] theorem coe_clamp (n m : Nat) : (clamp n m : Nat) = min n m := rfl

/-! ### findSome? -/

@[simp] theorem findSome?_zero {f : Fin 0 → Option α} : findSome? f = none := by simp [findSome?]

@[simp] theorem findSome?_one {f : Fin 1 → Option α} : findSome? f = f 0 := by simp [findSome?, foldl_succ]

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

@[simp, grind =]
theorem findSome?_eq_some_iff {f : Fin n → Option α} :
    findSome? f = some a ↔ ∃ i, f i = some a ∧ ∀ j < i, f j = none := by
  induction n with
  | zero =>
    simp only [findSome?_zero, (Option.some_ne_none _).symm, false_iff]
    exact fun  ⟨i, _⟩ => i.elim0
  | succ n ih =>
    simp only [findSome?_succ, Option.or_eq_some_iff, Fin.exists_fin_succ, Fin.forall_fin_succ,
      not_lt_zero, false_implies, implies_true, and_true, succ_lt_succ_iff, succ_pos,
      forall_const, ih, and_left_comm (b := f 0 = none), exists_and_left]

@[simp, grind =] theorem findSome?_eq_none_iff {f : Fin n → Option α} :
    findSome? f = none ↔ ∀ i, f i = none := by
  induction n with
  | zero =>
    simp only [findSome?_zero, true_iff]
    exact fun i => i.elim0
  | succ n ih =>
    simp only [findSome?_succ, Option.or_eq_none_iff, ih, forall_fin_succ]

theorem isNone_findSome?_iff {f : Fin n → Option α} :
    (findSome? f).isNone ↔ ∀ i, (f i).isNone := by simp

@[deprecated (since := "2025-09-28")]
alias findSome?_isNone_iff := isNone_findSome?_iff

@[simp] theorem isSome_findSome?_iff {f : Fin n → Option α} :
    (findSome? f).isSome ↔ ∃ i, (f i).isSome := by
  cases h : findSome? f with (simp only [findSome?_eq_none_iff, findSome?_eq_some_iff] at h; grind)

@[deprecated (since := "2025-09-28")]
alias findSome?_isSome_iff := isSome_findSome?_iff

theorem exists_minimal_of_findSome?_eq_some {f : Fin n → Option α}
    (h : findSome? f = some x) : ∃ i, f i = some x ∧ ∀ j < i, f j = none :=
  findSome?_eq_some_iff.1 h

theorem exists_eq_some_of_findSome?_eq_some {f : Fin n → Option α}
    (h : findSome? f = some x) : ∃ i, f i = some x := by grind

@[deprecated (since := "2025-09-28")]
alias exists_of_findSome?_eq_some := exists_eq_some_of_findSome?_eq_some

theorem eq_none_of_findSome?_eq_none {f : Fin n → Option α} (h : findSome? f = none) (i) :
    f i = none := findSome?_eq_none_iff.1 h i

theorem exists_isSome_of_isSome_findSome? {f : Fin n → Option α} (h : (findSome? f).isSome) :
    ∃ i, (f i).isSome := isSome_findSome?_iff.1 h

theorem isNone_of_isNone_findSome? {f : Fin n → Option α} (h : (findSome? f).isNone) :
    (f i).isNone := isNone_findSome?_iff.1 h i

theorem isSome_findSome?_of_isSome {f : Fin n → Option α} (h : (f i).isSome) :
    (findSome? f).isSome := isSome_findSome?_iff.2 ⟨_, h⟩

theorem map_findSome? (f : Fin n → Option α) (g : α → β) :
    (findSome? f).map g = findSome? (Option.map g <| f ·) := by
  induction n with
  | zero => rfl
  | succ n ih => simp [findSome?_succ, Function.comp_def, Option.map_or, ih]

theorem findSome?_guard {p : Fin n → Bool} : findSome? (Option.guard p) = find? p := rfl

theorem findSome?_eq_findSome?_finRange (f : Fin n → Option α) :
    findSome? f = (List.finRange n).findSome? f := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [findSome?_succ, List.finRange_succ, List.findSome?_cons]
    cases f 0 <;> simp [ih, List.findSome?_map, Function.comp_def]

/-! ### Fin.find? -/

@[simp] theorem find?_zero {p : Fin 0 → Bool} : find? p = none := by simp [find?]

@[simp] theorem find?_one {p : Fin 1 → Bool} : find? p = if p 0 then some 0 else none := by
  simp only [find?, findSome?_one, Fin.isValue]; rfl

theorem find?_succ {p : Fin (n+1) → Bool} :
    find? p = if p 0 then some 0 else (find? fun i => p i.succ).map Fin.succ := by
  simp only [find?, findSome?_succ, Option.guard, fun a => apply_ite (Option.or · a),
    Option.some_or, Option.none_or, map_findSome?, Option.map_if]

@[simp, grind =]
theorem find?_eq_some_iff {p : Fin n → Bool} :
    find? p = some i ↔ p i ∧ ∀ j, j < i → p j = false := by simp [find?, and_assoc]

theorem isSome_find?_iff {p : Fin n → Bool} :
    (find? p).isSome ↔ ∃ i, p i := by simp [find?]

@[deprecated (since := "2025-09-28")]
alias find?_isSome_iff := isSome_find?_iff

@[simp, grind =]
theorem find?_eq_none_iff {p : Fin n → Bool} : find? p = none ↔ ∀ i, p i = false := by simp [find?]

theorem isNone_find?_iff {p : Fin n → Bool} : (find? p).isNone ↔ ∀ i, p i = false := by simp [find?]

@[deprecated (since := "2025-09-28")]
alias find?_isNone_iff := isNone_find?_iff

theorem eq_true_of_find?_eq_some {p : Fin n → Bool} (h : find? p = some i) : p i :=
    (find?_eq_some_iff.mp h).1

theorem eq_false_of_find?_eq_some_of_lt {p : Fin n → Bool} (h : find? p = some i) :
    ∀ j < i, p j = false := (find?_eq_some_iff.mp h).2

theorem eq_false_of_find?_eq_none {p : Fin n → Bool} (h : find? p = none) (i) :
    p i = false := find?_eq_none_iff.1 h i

theorem exists_eq_true_of_isSome_find? {p : Fin n → Bool} (h : (find? p).isSome) :
    ∃ i, p i := isSome_find?_iff.1 h

theorem eq_false_of_isNone_find? {p : Fin n → Bool}  (h : (find? p).isNone) : p i = false :=
  isNone_find?_iff.1 h i

theorem isSome_find?_of_eq_true {p : Fin n → Bool}  (h : p i) :
    (find? p).isSome := isSome_find?_iff.2 ⟨_, h⟩

theorem get_find?_eq_true {p : Fin n → Bool} (h : (find? p).isSome) : p ((find? p).get h) :=
  eq_true_of_find?_eq_some (Option.some_get _).symm

theorem get_find?_minimal {p : Fin n → Bool}  (h : (find? p).isSome) :
    ∀ j, j < (find? p).get h → p j = false :=
  eq_false_of_find?_eq_some_of_lt (Option.some_get _).symm

theorem find?_eq_find?_finRange {p : Fin n → Bool} : find? p = (List.finRange n).find? p := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [find?_succ, List.finRange_succ, List.find?_cons]
    split <;> simp [Function.comp_def, *]

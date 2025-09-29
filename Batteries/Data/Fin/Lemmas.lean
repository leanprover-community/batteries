/-
Copyright (c) 2022 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Batteries.Data.Fin.Basic
import Batteries.Util.ProofWanted
import Batteries.Tactic.Alias

namespace Fin

attribute [norm_cast] val_last

/-! ### last -/

@[simp] theorem not_last_lt (a : Fin (n + 1)) : ¬(last n) < a := Fin.not_lt.mpr (le_last a)

/-! ### exists, forall -/

-- TODO: deprecate duplicates in Mathlib

theorem forall_fin_succ_last {P : Fin (n + 1) → Prop} :
    (∀ i, P i) ↔ P (.last _) ∧ (∀ i : Fin n, P i.castSucc) :=
  ⟨fun H => ⟨H _, fun _ => H _⟩, fun ⟨H0, H1⟩ i => i.lastCases H0 H1⟩

theorem exists_fin_succ_last {P : Fin (n + 1) → Prop} :
    (∃ i, P i) ↔ P (.last _) ∨ (∃ i : Fin n, P i.castSucc) :=
  ⟨fun ⟨i, h⟩ => i.lastCases Or.inl (fun i hi => Or.inr ⟨i, hi⟩) h,
    fun h => h.elim (fun h => ⟨_, h⟩) (fun ⟨_, hi⟩ => ⟨_, hi⟩)⟩

/-! ### foldl/foldr -/

theorem foldl_assoc {op : α → α → α} [ha : Std.Associative op] {f : Fin n → α} {a₁ a₂} :
    foldl n (fun x i => op x (f i)) (op a₁ a₂) = op a₁ (foldl n (fun x i => op x (f i)) a₂) := by
  induction n generalizing a₂ with
  | zero => rfl
  | succ n ih => simp only [foldl_succ, ha.assoc, ih]

theorem foldr_assoc {op : α → α → α} [ha : Std.Associative op] {f : Fin n → α} {a₁ a₂} :
    foldr n (fun i x => op (f i) x) (op a₁ a₂) = op (foldr n (fun i x => op (f i) x) a₁) a₂ := by
  simp only [← Fin.foldl_rev]
  haveI : Std.Associative (flip op) := ⟨fun a b c => (ha.assoc c b a).symm⟩
  exact foldl_assoc (op := flip op)

theorem foldr_assoc_flip {op : α → α → α} [ha : Std.Associative op] {f : Fin n → α} {a₁ a₂} :
    foldr n (fun i x => op x (f i)) (op a₁ a₂) = op a₁ (foldr n (fun i x => op x (f i)) a₂) := by
  simp only [← Fin.foldl_rev, foldl_assoc]

theorem foldl_assoc_flip {op : α → α → α} [ha : Std.Associative op] {f : Fin n → α} {a₁ a₂} :
    foldl n (fun x i => op (f i) x) (op a₁ a₂) = op (foldl n (fun x i => op (f i) x) a₁) a₂ := by
  simp only [← Fin.foldr_rev, foldr_assoc]

/-! ### clamp -/

@[simp] theorem coe_clamp (n m : Nat) : (clamp n m : Nat) = min n m := rfl

/-! ### findSome? -/

@[simp] theorem findSome?_zero {f : Fin 0 → Option α} : findSome? f = none := rfl

@[simp] theorem findSome?_one {f : Fin 1 → Option α} : findSome? f = f 0 := rfl

theorem findSome?_succ {f : Fin (n+1) → Option α} :
    findSome? f = (f 0).or (findSome? fun i => f i.succ) := by
  simp only [findSome?, foldl_succ, Option.orElse_eq_orElse, Option.orElse_eq_or]
  exact Eq.trans (by cases (f 0) <;> rfl) foldl_assoc

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
    exact fun ⟨i, _⟩ => i.elim0
  | succ n ih =>
    simp only [findSome?_succ, Option.or_eq_some_iff, exists_fin_succ, forall_fin_succ,
      succ_lt_succ_iff, succ_pos, not_lt_zero, ih]
    grind

@[simp, grind =] theorem findSome?_eq_none_iff {f : Fin n → Option α} :
    findSome? f = none ↔ ∀ i, f i = none := by
  induction n with
  | zero =>
    simp only [findSome?_zero, true_iff]; exact fun i => i.elim0
  | succ n ih => simp only [findSome?_succ, Option.or_eq_none_iff, ih, forall_fin_succ]

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
  | succ n ih => simp [findSome?_succ, Option.map_or, ih]

theorem findSome?_guard {p : Fin n → Bool} : findSome? (Option.guard p) = find? p := rfl

theorem findSome?_eq_findSome?_finRange (f : Fin n → Option α) :
    findSome? f = (List.finRange n).findSome? f := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [findSome?_succ, List.finRange_succ, List.findSome?_cons]
    cases f 0 <;> simp [ih, List.findSome?_map, Function.comp_def]

/-! ### find? -/

@[simp] theorem find?_zero {p : Fin 0 → Bool} : find? p = none := rfl

@[simp] theorem find?_one {p : Fin 1 → Bool} : find? p = if p 0 then some 0 else none := rfl

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

theorem eq_false_of_isNone_find? {p : Fin n → Bool} (h : (find? p).isNone) : p i = false :=
  isNone_find?_iff.1 h i

theorem isSome_find?_of_eq_true {p : Fin n → Bool} (h : p i) :
    (find? p).isSome := isSome_find?_iff.2 ⟨_, h⟩

theorem map_find? (f : Fin n → Bool) (g : Fin n → Fin n) :
    (find? p).map g = find? (p <| g ·) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [find?_succ, apply_ite (Option.map g ·), Option.map_some, Option.map_map]

theorem get_find?_eq_true {p : Fin n → Bool} (h : (find? p).isSome) : p ((find? p).get h) :=
  eq_true_of_find?_eq_some (Option.some_get _).symm

theorem get_find?_minimal {p : Fin n → Bool} (h : (find? p).isSome) :
    ∀ j, j < (find? p).get h → p j = false :=
  eq_false_of_find?_eq_some_of_lt (Option.some_get _).symm

theorem find?_eq_find?_finRange {p : Fin n → Bool} : find? p = (List.finRange n).find? p :=
  (findSome?_eq_findSome?_finRange _).trans (List.findSome?_guard)

theorem exists_eq_true_iff_exists_minimal_eq_true (p : Fin n → Bool):
    (∃ i, p i) ↔ ∃ i, p i ∧ ∀ j < i, p j = false := by cases h : find? p <;> grind

theorem exists_iff_exists_minimal (p : Fin n → Prop) [DecidablePred p] :
    (∃ i, p i) ↔ ∃ i, p i ∧ ∀ j < i, ¬ p j := by cases h : find? (p ·) <;> grind

/-! ### findSomeRev? -/

@[simp] theorem findSomeRev?_zero {f : Fin 0 → Option α} : findSomeRev? f = none := rfl

@[simp] theorem findSomeRev?_one {f : Fin 1 → Option α} : findSomeRev? f = f 0 := rfl

theorem findSomeRev?_succ {f : Fin (n+1) → Option α} :
    findSomeRev? f = (f (last n)).or (findSomeRev? fun i => f i.castSucc) := by
  simp only [findSomeRev?, foldr_succ_last, Option.orElse_eq_orElse, Option.orElse_eq_or]
  exact Eq.trans (by cases (f (last n)) <;> rfl) foldr_assoc_flip

theorem findSomeRev?_succ_of_some {f : Fin (n+1) → Option α} (h : f (last n) = some x) :
    findSomeRev? f = some x := by simp [findSomeRev?_succ, h]

theorem findSomeRev?_succ_of_isSome {f : Fin (n+1) → Option α} (h : (f (last n)).isSome) :
    findSomeRev? f = f (last n) := by
  cases _h : f (last n) <;> simp_all [findSomeRev?_succ_of_some]

theorem findSomeRev?_succ_of_none {f : Fin (n+1) → Option α} (h : f (last n) = none) :
    findSomeRev? f = findSomeRev? fun i => f i.castSucc := by simp [findSomeRev?_succ, h]

theorem findSomeRev?_succ_of_isNone {f : Fin (n+1) → Option α} (h : (f (last n)).isNone) :
    findSomeRev? f = findSomeRev? fun i => f i.castSucc := by simp_all [findSomeRev?_succ_of_none]

@[simp, grind =]
theorem findSomeRev?_eq_some_iff {f : Fin n → Option α} :
    findSomeRev? f = some a ↔ ∃ i, f i = some a ∧ ∀ j, i < j → f j = none := by
  induction n with
  | zero =>
    simp only [findSomeRev?_zero, (Option.some_ne_none _).symm, false_iff]
    exact fun  ⟨i, _⟩ => i.elim0
  | succ n ih =>
    simp only [findSomeRev?_succ, Option.or_eq_some_iff, forall_fin_succ_last, exists_fin_succ_last,
      castSucc_lt_castSucc_iff, castSucc_lt_last, not_last_lt, ih]
    grind

@[simp, grind =] theorem findSomeRev?_eq_none_iff {f : Fin n → Option α} :
    findSomeRev? f = none ↔ ∀ i, f i = none := by
  induction n with
  | zero =>
    simp only [findSomeRev?_zero, true_iff]
    exact fun i => i.elim0
  | succ n ih => simp only [findSomeRev?_succ, Option.or_eq_none_iff, ih, forall_fin_succ_last]

theorem isNone_findSomeRev?_iff {f : Fin n → Option α} :
    (findSomeRev? f).isNone ↔ ∀ i, (f i).isNone := by simp

@[simp] theorem isSome_findSomeRev?_iff {f : Fin n → Option α} :
    (findSomeRev? f).isSome ↔ ∃ i, (f i).isSome := by
  cases h : findSomeRev? f with
    (simp only [findSomeRev?_eq_none_iff, findSomeRev?_eq_some_iff] at h; grind)

theorem exists_minimal_of_findSomeRev?_eq_some {f : Fin n → Option α}
    (h : findSomeRev? f = some x) : ∃ i, f i = some x ∧ ∀ j, i < j → f j = none :=
  findSomeRev?_eq_some_iff.1 h

theorem exists_eq_some_of_findSomeRev?_eq_some {f : Fin n → Option α}
    (h : findSomeRev? f = some x) : ∃ i, f i = some x := by grind

theorem eq_none_of_findSomeRev?_eq_none {f : Fin n → Option α} (h : findSomeRev? f = none) (i) :
    f i = none := findSomeRev?_eq_none_iff.1 h i

theorem exists_isSome_of_isSome_findSomeRev? {f : Fin n → Option α} (h : (findSomeRev? f).isSome) :
    ∃ i, (f i).isSome := isSome_findSomeRev?_iff.1 h

theorem isNone_of_isNone_findSomeRev? {f : Fin n → Option α} (h : (findSomeRev? f).isNone) :
    (f i).isNone := isNone_findSomeRev?_iff.1 h i

theorem isSome_findSomeRev?_of_isSome {f : Fin n → Option α} (h : (f i).isSome) :
    (findSomeRev? f).isSome := isSome_findSomeRev?_iff.2 ⟨_, h⟩

theorem map_findSomeRev? (f : Fin n → Option α) (g : α → β) :
    (findSomeRev? f).map g = findSomeRev? (Option.map g <| f ·) := by
  induction n with
  | zero => rfl
  | succ n ih => simp [findSomeRev?_succ, Option.map_or, ih]

theorem findSomeRev?_guard {p : Fin n → Bool} : findSomeRev? (Option.guard p) = findRev? p := rfl

/-! ### findRev? -/

@[simp] theorem findRev?_zero {p : Fin 0 → Bool} : findRev? p = none := rfl

@[simp] theorem findRev?_one {p : Fin 1 → Bool} : findRev? p = if p 0 then some 0 else none := rfl

theorem findRev?_succ {p : Fin (n+1) → Bool} :
    findRev? p = if p (last n) then some (last n)
    else (findRev? fun i => p i.castSucc).map Fin.castSucc := by
  simp only [findRev?, findSomeRev?_succ, Option.guard, fun a => apply_ite (Option.or · a),
    Option.some_or, Option.none_or, map_findSomeRev?, Option.map_if]

@[simp, grind =]
theorem findRev?_eq_some_iff {p : Fin n → Bool} :
    findRev? p = some i ↔ p i ∧ ∀ j, i < j → p j = false := by simp [findRev?, and_assoc]

theorem isSome_findRev?_iff {p : Fin n → Bool} :
    (findRev? p).isSome ↔ ∃ i, p i := by simp [findRev?]

@[simp, grind =]
theorem findRev?_eq_none_iff {p : Fin n → Bool} : findRev? p = none ↔ ∀ i, p i = false := by
  simp [findRev?]

theorem isNone_findRev?_iff {p : Fin n → Bool} : (findRev? p).isNone ↔ ∀ i, p i = false := by
  simp [findRev?]

theorem eq_true_of_findRev?_eq_some {p : Fin n → Bool} (h : findRev? p = some i) : p i :=
    (findRev?_eq_some_iff.mp h).1

theorem eq_false_of_findRev?_eq_some_of_lt {p : Fin n → Bool} (h : findRev? p = some i) :
    ∀ j, i < j → p j = false := (findRev?_eq_some_iff.mp h).2

theorem eq_false_of_findRev?_eq_none {p : Fin n → Bool} (h : findRev? p = none) (i) :
    p i = false := findRev?_eq_none_iff.1 h i

theorem exists_eq_true_of_isSome_findRev? {p : Fin n → Bool} (h : (findRev? p).isSome) :
    ∃ i, p i := isSome_findRev?_iff.1 h

theorem eq_false_of_isNone_findRev? {p : Fin n → Bool} (h : (findRev? p).isNone) : p i = false :=
  isNone_findRev?_iff.1 h i

theorem isSome_findRev?_of_eq_true {p : Fin n → Bool} (h : p i) :
    (findRev? p).isSome := isSome_findRev?_iff.2 ⟨_, h⟩

theorem get_findRev?_eq_true {p : Fin n → Bool} (h : (findRev? p).isSome) :
    p ((findRev? p).get h) := eq_true_of_findRev?_eq_some (Option.some_get _).symm

theorem get_findRev?_minimal {p : Fin n → Bool} (h : (findRev? p).isSome) :
    ∀ j, (findRev? p).get h < j → p j = false :=
  eq_false_of_findRev?_eq_some_of_lt (Option.some_get _).symm

theorem exists_eq_true_iff_exists_maximal_eq_true (p : Fin n → Bool):
    (∃ i, p i) ↔ ∃ i, p i ∧ ∀ j , i < j → p j = false := by cases h : findRev? p <;> grind

theorem exists_iff_exists_maximal (p : Fin n → Prop) [DecidablePred p] :
    (∃ i, p i) ↔ ∃ i, p i ∧ ∀ j, i < j → ¬ p j := by cases h : findRev? (p ·) <;> grind

theorem find?_le_findRev? {p : Fin n → Bool} : find? p ≤ findRev? p := by
  cases hl : find? p with | none => exact Option.none_le | some l =>
  rw [find?_eq_some_iff] at hl; cases hu : findRev? p with
  | none => simp only [findRev?_eq_none_iff] at hu; grind
  | some u => simp only [findRev?_eq_some_iff] at hu; grind

theorem map_rev_findRev? {p : Fin n → Bool} : findRev? p = Fin.rev <$> find? fun i => p i.rev := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [findRev?_succ, find?_succ, apply_ite (rev <$> ·), Option.map_eq_map,
      Option.map_some, rev_zero, Fin.rev_succ, Option.map_map, Function.comp_def, ih]

/-
Copyright (c) 2022 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Batteries.Data.Fin.Basic
public import Batteries.Data.Nat.Lemmas
public import Batteries.Util.ProofWanted
public import Batteries.Tactic.Alias

@[expose] public section

namespace Fin

attribute [norm_cast] val_last

/-! ### rev -/

attribute [grind] rev_lt_rev rev_le_rev rev_rev

/-! ### foldl/foldr -/

theorem foldl_assoc {op : α → α → α} [ha : Std.Associative op] {f : Fin n → α} {a₁ a₂} :
    foldl n (fun x i => op x (f i)) (op a₁ a₂) = op a₁ (foldl n (fun x i => op x (f i)) a₂) := by
  induction n generalizing a₂ with
  | zero => simp
  | succ n ih => simp only [foldl_succ, ha.assoc, ih]

theorem foldr_assoc {op : α → α → α} [ha : Std.Associative op] {f : Fin n → α} {a₁ a₂} :
    foldr n (fun i x => op (f i) x) (op a₁ a₂) = op (foldr n (fun i x => op (f i) x) a₁) a₂ := by
  simp only [← Fin.foldl_rev]
  haveI : Std.Associative (flip op) := ⟨fun a b c => (ha.assoc c b a).symm⟩
  exact foldl_assoc (op := flip op)

/-! ### clamp -/

@[simp] theorem coe_clamp (n m : Nat) : (clamp n m : Nat) = min n m := rfl

/-! ### findSome? -/

@[simp] theorem findSome?_zero {f : Fin 0 → Option α} : findSome? f = none := by simp [findSome?]

@[simp] theorem findSome?_one {f : Fin 1 → Option α} : findSome? f = f 0 := by
  simp [findSome?, foldl_succ]

theorem findSome?_succ {f : Fin (n+1) → Option α} :
    findSome? f = (f 0).or (findSome? (f ·.succ)) := by
  simp only [findSome?, foldl_succ, Option.orElse_eq_orElse, Option.orElse_eq_or]
  exact Eq.trans (by cases (f 0) <;> rfl) foldl_assoc

theorem findSome?_succ_of_some {f : Fin (n+1) → Option α} (h : f 0 = some x) :
    findSome? f = some x := findSome?_succ.trans (h ▸ Option.some_or)

theorem findSome?_succ_of_isSome {f : Fin (n+1) → Option α} (h : (f 0).isSome) :
    findSome? f = f 0 := findSome?_succ.trans (Option.or_of_isSome h)

theorem findSome?_succ_of_none {f : Fin (n+1) → Option α} (h : f 0 = none) :
    findSome? f = findSome? (f ·.succ) := findSome?_succ.trans (Option.or_eq_right_of_none h)

theorem findSome?_succ_of_isNone {f : Fin (n+1) → Option α} (h : (f 0).isNone) :
    findSome? f = findSome? (f ·.succ) := findSome?_succ.trans (Option.or_of_isNone h)

@[simp, grind =]
theorem findSome?_eq_some_iff {f : Fin n → Option α} :
    findSome? f = some a ↔ ∃ i, f i = some a ∧ ∀ j < i, f j = none := by
  induction n with
  | zero =>
    simp only [findSome?_zero, reduceCtorEq, forall_fin_zero, and_true, exists_fin_zero]
  | succ n ih =>
    simp only [findSome?_succ, Option.or_eq_some_iff, exists_fin_succ, forall_fin_succ,
      succ_lt_succ_iff, succ_pos, not_lt_zero, ih]
    grind

@[simp, grind =] theorem findSome?_eq_none_iff {f : Fin n → Option α} :
    findSome? f = none ↔ ∀ i, f i = none := by
  induction n with
  | zero => simp only [findSome?_zero, forall_fin_zero]
  | succ n ih => simp only [findSome?_succ, Option.or_eq_none_iff, ih, forall_fin_succ]

theorem isNone_findSome?_iff {f : Fin n → Option α} :
    (findSome? f).isNone ↔ ∀ i, (f i).isNone := by simp

@[deprecated (since := "2025-09-28")]
alias findSome?_isNone_iff := isNone_findSome?_iff

@[simp] theorem isSome_findSome?_iff {f : Fin n → Option α} :
    (findSome? f).isSome ↔ ∃ i, (f i).isSome := by
  cases h : findSome? f <;> grind

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
  | zero => simp
  | succ n ih => simp [findSome?_succ, Option.map_or, ih]

theorem findSome?_guard {p : Fin n → Bool} : findSome? (Option.guard p) = find? p := rfl

theorem bind_findSome?_guard_isSome {f : Fin n → Option α} :
    (findSome? (Option.guard fun i => (f i).isSome)).bind f = findSome? f := by

  cases hf : findSome? f with
  | none => grind
  | some x =>
    simp only [Option.bind_eq_some_iff, findSome?_eq_some_iff, Option.guard_eq_some_iff]
    grind

theorem findSome?_eq_findSome?_finRange (f : Fin n → Option α) :
    findSome? f = (List.finRange n).findSome? f := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [findSome?_succ, List.finRange_succ, List.findSome?_cons]
    cases f 0 <;> simp [ih, List.findSome?_map, Function.comp_def]

/-! ### findSomeRev? -/

@[simp]
theorem findSome?_rev {f : Fin n → Option α} : findSome? (f ·.rev) = findSomeRev? f := rfl

@[simp]
theorem findSomeRev?_rev {f : Fin n → Option α} :
    findSomeRev? (f ·.rev) = findSome? f := by simp only [findSomeRev?, rev_rev]

@[simp] theorem findSomeRev?_zero {f : Fin 0 → Option α} : findSomeRev? f = none := by
  simp [findSomeRev?]

@[simp] theorem findSomeRev?_one {f : Fin 1 → Option α} : findSomeRev? f = f 0 := by
  simp [findSomeRev?]

theorem findSomeRev?_succ {f : Fin (n+1) → Option α} :
    findSomeRev? f = (f (last n)).or (findSomeRev? fun i => f i.castSucc) := by
  unfold findSomeRev?
  simp only [findSome?_succ, rev_succ, rev_zero]

@[simp, grind =]
theorem findSomeRev?_eq_some_iff {f : Fin n → Option α} :
    findSomeRev? f = some a ↔ ∃ i, f i = some a ∧ ∀ j, i < j → f j = none :=
  findSome?_eq_some_iff.trans <| ⟨fun ⟨i, h⟩ => ⟨i.rev, by grind,
    fun j hj => have := h.2 j.rev; by grind⟩, fun ⟨i, _⟩ => ⟨i.rev, by grind⟩⟩

@[simp, grind =] theorem findSomeRev?_eq_none_iff {f : Fin n → Option α} :
    findSomeRev? f = none ↔ ∀ i, f i = none :=
  findSome?_eq_none_iff.trans <| ⟨fun h i => have := h i.rev; by grind, by grind⟩

theorem isNone_findSomeRev?_iff {f : Fin n → Option α} :
    (findSomeRev? f).isNone ↔ ∀ i, (f i).isNone := by simp

@[simp] theorem isSome_findSomeRev?_iff {f : Fin n → Option α} :
    (findSomeRev? f).isSome ↔ ∃ i, (f i).isSome := by
  cases h : findSomeRev? f <;> grind

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
  | zero => grind [findSomeRev?_zero]
  | succ n ih => grind [findSomeRev?_succ]

@[grind =_]
theorem findSomeRev?_guard {p : Fin n → Bool} : findSomeRev? (Option.guard p) = findRev? p := rfl

theorem bind_findSomeRev?_guard_isSome {f : Fin n → Option α} :
    (findSomeRev? (Option.guard fun i => (f i).isSome)).bind f = findSomeRev? f := by
  cases hf : findSomeRev? f with
  | none => grind
  | some x =>
    simp only [Option.bind_eq_some_iff, findSomeRev?_eq_some_iff, Option.guard_eq_some_iff]
    grind

/-! ### find? -/

@[simp] theorem find?_zero {p : Fin 0 → Bool} : find? p = none := by simp

@[simp] theorem find?_one {p : Fin 1 → Bool} : find? p = if p 0 then some 0 else none := by
  simp [Option.guard]

theorem find?_succ {p : Fin (n+1) → Bool} :
    find? p = if p 0 then some 0 else (find? (p ·.succ)).map Fin.succ := by
  simp only [findSome?_succ, Option.guard, fun a => apply_ite (Option.or · a),
    Option.some_or, Option.none_or, map_findSome?, Option.map_if]

@[simp, grind =]
theorem find?_eq_some_iff {p : Fin n → Bool} :
    find? p = some i ↔ p i ∧ ∀ j, j < i → p j = false := by simp [and_assoc]

theorem isSome_find?_iff {p : Fin n → Bool} :
    (find? p).isSome ↔ ∃ i, p i := by simp

@[deprecated (since := "2025-09-28")]
alias find?_isSome_iff := isSome_find?_iff

@[simp, grind =]
theorem find?_eq_none_iff {p : Fin n → Bool} : find? p = none ↔ ∀ i, p i = false := by simp

theorem isNone_find?_iff {p : Fin n → Bool} : (find? p).isNone ↔ ∀ i, p i = false := by simp

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

theorem get_find?_eq_true {p : Fin n → Bool} (h : (find? p).isSome) : p ((find? p).get h) :=
  eq_true_of_find?_eq_some (Option.some_get _).symm

theorem get_find?_minimal {p : Fin n → Bool} (h : (find? p).isSome) :
    ∀ j, j < (find? p).get h → p j = false :=
  eq_false_of_find?_eq_some_of_lt (Option.some_get _).symm

theorem bind_find?_isSome {f : Fin n → Option α} :
    (find? (fun i => (f i).isSome)).bind f = findSome? f := bind_findSome?_guard_isSome

theorem find?_eq_find?_finRange {p : Fin n → Bool} : find? p = (List.finRange n).find? p :=
  (findSome?_eq_findSome?_finRange _).trans (List.findSome?_guard)

theorem exists_eq_true_iff_exists_minimal_eq_true (p : Fin n → Bool):
    (∃ i, p i) ↔ ∃ i, p i ∧ ∀ j < i, p j = false := by cases h : find? p <;> grind

theorem exists_iff_exists_minimal (p : Fin n → Prop) [DecidablePred p] :
    (∃ i, p i) ↔ ∃ i, p i ∧ ∀ j < i, ¬ p j := by cases h : find? (p ·) <;> grind

theorem find?_rev {p : Fin n → Bool} : find? (p ·.rev) = (findRev? p).map rev := by
  simp [← findSomeRev?_rev, map_findSomeRev?, Option.guard_eq_ite]

theorem map_rev_findRev? {p : Fin n → Bool} : (findRev? (p ·.rev)).map rev = find? p := by
  simp only [← find?_rev, rev_rev]

/-! ### findRev? -/

@[simp] theorem findRev?_zero {p : Fin 0 → Bool} : findRev? p = none := by grind

theorem findRev?_succ {p : Fin (n+1) → Bool} :
    findRev? p = if p (last n) then some (last n)
    else (findRev? fun i => p i.castSucc).map Fin.castSucc := by
  simp only [findSomeRev?_succ, Option.guard, fun a => apply_ite (Option.or · a),
    Option.some_or, Option.none_or, map_findSomeRev?, Option.map_if]

@[simp] theorem findRev?_one {p : Fin 1 → Bool} : findRev? p = if p 0 then some 0 else none := by
  grind [findRev?_succ]

@[simp, grind =]
theorem findRev?_eq_some_iff {p : Fin n → Bool} :
    findRev? p = some i ↔ p i ∧ ∀ j, i < j → p j = false := by simp [and_assoc]

@[simp, grind =]
theorem findRev?_eq_none_iff {p : Fin n → Bool} : findRev? p = none ↔ ∀ i, p i = false := by simp

theorem isSome_findRev?_iff {p : Fin n → Bool} :
    (findRev? p).isSome ↔ ∃ i, p i := by simp

theorem isNone_findRev?_iff {p : Fin n → Bool} : (findRev? p).isNone ↔ ∀ i, p i = false := by simp

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

theorem get_findRev?_maximal {p : Fin n → Bool} (h : (findRev? p).isSome) :
    ∀ j, (findRev? p).get h < j → p j = false :=
  eq_false_of_findRev?_eq_some_of_lt (Option.some_get _).symm

theorem exists_eq_true_iff_exists_maximal_eq_true (p : Fin n → Bool):
    (∃ i, p i) ↔ ∃ i, p i ∧ ∀ j , i < j → p j = false := by cases h : findRev? p <;> grind

theorem exists_iff_exists_maximal (p : Fin n → Prop) [DecidablePred p] :
    (∃ i, p i) ↔ ∃ i, p i ∧ ∀ j, i < j → ¬ p j := by cases h : findRev? (p ·) <;> grind

theorem bind_findRev?_isSome {f : Fin n → Option α} :
    (findRev? (fun i => (f i).isSome)).bind f = findSomeRev? f := bind_findSomeRev?_guard_isSome

theorem findRev?_rev {p : Fin n → Bool} : findRev? (p ·.rev) = (find? p).map rev := by
  simp [← findSome?_rev, map_findSome?, Option.guard_eq_ite]

theorem map_rev_find? {p : Fin n → Bool} : (find? (p ·.rev)).map rev = findRev? p := by
  simp only [← findRev?_rev, rev_rev]

theorem find?_le_findRev? {p : Fin n → Bool} : find? p ≤ findRev? p := by
  cases hl : find? p <;> cases hu : findRev? p <;> grind

theorem find?_eq_findRev?_iff {p : Fin n → Bool} : find? p = findRev? p ↔
    ∀ i j, p i = true → p j = true → i = j := by
  cases h : findRev? p <;> grind

/-! ### divNat / modNat / mkDivMod -/

@[simp] theorem coe_divNat (i : Fin (m * n)) : (i.divNat : Nat) = i / n := rfl

@[simp] theorem coe_modNat (i : Fin (m * n)) : (i.modNat : Nat) = i % n := rfl

@[simp] theorem coe_mkDivMod (i : Fin m) (j : Fin n) : (mkDivMod i j : Nat) = n * i + j := rfl

@[simp] theorem divNat_mkDivMod (i : Fin m) (j : Fin n) : (mkDivMod i j).divNat = i := by
  ext; simp [Nat.mul_add_div (Nat.zero_lt_of_lt j.is_lt)]

@[simp] theorem modNat_mkDivMod (i : Fin m) (j : Fin n) : (mkDivMod i j).modNat = j := by
  ext; simp [Nat.mod_eq_of_lt]

@[simp] theorem divNat_mkDivMod_modNat (k : Fin (m * n)) :
    mkDivMod k.divNat k.modNat = k := by ext; simp [Nat.div_add_mod]

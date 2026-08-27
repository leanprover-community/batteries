/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Mario Carneiro
-/
module

public import Batteries.Data.AssocList.Basic

@[expose] public section

/-!
# Lemmas about association lists

Each operation on `AssocList` is specified by a lemma relating it to the corresponding
operation on `List (α × β)`, transported along `AssocList.toList`.
-/

namespace Batteries

namespace AssocList

@[simp] theorem empty_eq : (∅ : AssocList α β) = nil := rfl

@[simp] theorem isEmpty_eq (l : AssocList α β) : isEmpty l = l.toList.isEmpty := by
  cases l <;> simp [*, isEmpty, List.isEmpty]

@[simp] theorem length_nil : length (nil : AssocList α β) = 0 := rfl
@[simp] theorem length_cons : length (cons a b t) = length t + 1 := rfl

theorem length_toList (l : AssocList α β) : l.toList.length = l.length := by
  induction l <;> simp_all

@[simp] theorem forM_eq [Monad m] (f : α → β → m PUnit) (l) :
    forM f l = l.toList.forM (fun (a, b) => f a b) := by
  induction l <;> simp [*, forM]

@[simp] theorem toList_mapKey (f : α → δ) (l : AssocList α β) :
    (mapKey f l).toList = l.toList.map (fun (a, b) => (f a, b)) := by
  induction l <;> simp [*]

@[simp] theorem length_mapKey : (mapKey f l).length = l.length := by
  induction l <;> simp_all

@[simp] theorem toList_mapVal (f : α → β → δ) (l : AssocList α β) :
    (mapVal f l).toList = l.toList.map (fun (a, b) => (a, f a b)) := by
  induction l <;> simp [*]

@[simp] theorem length_mapVal : (mapVal f l).length = l.length := by
  induction l <;> simp_all

@[simp] theorem filterMapVal_nil : filterMapVal f nil = nil := rfl

theorem filterMapVal_cons (f : α → β → Option γ) (k) (v) (t) :
    filterMapVal f (.cons k v t) =
      match f k v with
      | none => filterMapVal f t
      | some d => .cons k d (filterMapVal f t) := rfl

@[simp] theorem toList_filterMapVal (f : α → β → Option δ) (l : AssocList α β) :
    (filterMapVal f l).toList =
      l.toList.filterMap (fun (a, b) => (f a b).map fun v => (a, v)) := by
  induction l with
  | nil => simp
  | cons k v t ih =>
    revert ih
    simp only [filterMapVal, toList, List.filterMap_cons]
    match f k v with
    | none
    | some d => simp

theorem length_filterMapVal_le : (filterMapVal f l).length ≤ l.length := by
  induction l with
  | nil => simp
  | cons k v t ih =>
    simp_all only [filterMapVal, length_cons]
    match f k v with
    | none => exact Nat.le_trans ih (Nat.le_succ _)
    | some _ => exact Nat.succ_le_succ ih

@[simp] theorem findEntryP?_eq (p : α → β → Bool) (l : AssocList α β) :
    findEntryP? p l = l.toList.find? fun (a, b) => p a b := by
  induction l <;> simp [findEntryP?, List.find?_cons]; split <;> simp [*]

@[simp] theorem findEntry?_eq [BEq α] (a : α) (l : AssocList α β) :
    findEntry? a l = l.toList.find? (·.1 == a) := findEntryP?_eq ..

theorem find?_eq_findEntry? [BEq α] (a : α) (l : AssocList α β) :
    find? a l = (l.findEntry? a).map (·.2) := by
  induction l <;> simp [find?, List.find?_cons]; split <;> simp [*]

theorem find?_eq [BEq α] (a : α) (l : AssocList α β) :
    find? a l = (l.toList.find? (·.1 == a)).map (·.2) := by simp [find?_eq_findEntry?]

@[simp] theorem any_eq (p : α → β → Bool) (l : AssocList α β) :
    any p l = l.toList.any fun (a, b) => p a b := by induction l <;> simp [any, *]

@[simp] theorem all_eq (p : α → β → Bool) (l : AssocList α β) :
    all p l = l.toList.all fun (a, b) => p a b := by induction l <;> simp [all, *]

@[simp] theorem contains_eq [BEq α] (a : α) (l : AssocList α β) :
    contains a l = l.toList.any (·.1 == a) := by
  induction l <;> simp [*, contains]

@[simp] theorem toList_replace [BEq α] (a : α) (b : β) (l : AssocList α β) :
    (replace a b l).toList =
    l.toList.replaceF (bif ·.1 == a then some (a, b) else none) := by
  induction l <;> simp [replace]; split <;> simp [*]

@[simp] theorem length_replace [BEq α] {a : α} : (replace a b l).length = l.length := by
  induction l
  · rfl
  · simp only [replace, length_cons]
    split <;> simp_all

@[simp] theorem toList_eraseP (p) (l : AssocList α β) :
    (eraseP p l).toList = l.toList.eraseP fun (a, b) => p a b := by
  induction l <;> simp [List.eraseP, cond]; split <;> simp [*]

@[simp] theorem toList_erase [BEq α] (a : α) (l : AssocList α β) :
    (erase a l).toList = l.toList.eraseP (·.1 == a) := toList_eraseP ..

@[simp] theorem toList_modify [BEq α] (a : α) (l : AssocList α β) :
    (modify a f l).toList =
    l.toList.replaceF fun (k, v) => bif k == a then some (a, f k v) else none := by
  simp [cond]
  induction l with simp [List.replaceF]
  | cons k v es ih => cases k == a <;> simp [ih]

@[simp] theorem length_modify [BEq α] {a : α} : (modify a f l).length = l.length := by
  induction l
  · rfl
  · simp only [modify, length_cons]
    split <;> simp_all

@[simp] theorem forIn_eq [Monad m] (l : AssocList α β) (init : δ)
    (f : (α × β) → δ → m (ForInStep δ)) : forIn l init f = forIn l.toList init f := by
  simp only [forIn]
  induction l generalizing init <;> simp [AssocList.forIn]
  congr; funext a; split <;> simp [*]

@[simp] theorem _root_.List.toList_toAssocList (l : List (α × β)) : l.toAssocList.toList = l := by
  induction l <;> simp [*]

@[simp] theorem toList_toAssocList (l : AssocList α β) : l.toList.toAssocList = l := by
  induction l <;> simp [*]

@[simp] theorem _root_.List.length_toAssocList (l : List (α × β)) :
    l.toAssocList.length = l.length := by
  induction l <;> simp [*]

@[simp] theorem beq_nil₂ [BEq α] [BEq β] : ((.nil : AssocList α β) == .nil) = true := rfl
@[simp] theorem beq_nil_cons [BEq α] [BEq β] : ((.nil : AssocList α β) == .cons a b t) = false :=
  rfl
@[simp] theorem beq_cons_nil [BEq α] [BEq β] : ((.cons a b t : AssocList α β) == .nil) = false :=
  rfl
@[simp] theorem beq_cons₂ [BEq α] [BEq β] :
    ((.cons a b t : AssocList α β) == .cons a' b' t') = (a == a' && b == b' && t == t') := rfl

instance [BEq α] [LawfulBEq α] [BEq β] [LawfulBEq β] : LawfulBEq (AssocList α β) where
  rfl {L} := by induction L <;> simp_all
  eq_of_beq {L M} := by
    induction L generalizing M with
    | nil => cases M <;> simp_all
    | cons a b L ih =>
      cases M with
      | nil => simp_all
      | cons a' b' M =>
        simp_all only [beq_cons₂, Bool.and_eq_true, beq_iff_eq, cons.injEq, true_and, and_imp]
        exact fun _ _ => ih

protected theorem beq_eq [BEq α] [BEq β] {l m : AssocList α β} :
    (l == m) = (l.toList == m.toList) := by
  simp [(· == ·)]
  induction l generalizing m <;> cases m <;> simp [*, (· == ·), AssocList.beq, List.beq]

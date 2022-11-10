/-
Copyright (c) 2022 Wojciech Nawrocki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Nawrocki
-/
import Std.Data.HashMap.Basic
import Std.Data.HashMap.WF
import Std.Data.List.Lemmas
import Std.Data.List.Perm
import Std.Data.Array.Lemmas

/-- If there is at most one element with the property `p`, erasing one such element is the same
as filtering out all of them. -/
theorem List.eraseP_eq_filter_of_unique (l : List α) (p : α → Bool)
    : l.Pairwise (p · → !p ·) → l.eraseP p = l.filter (!p ·) := by
  intro h
  induction l with
  | nil => rfl
  | cons x xs ih =>
    specialize ih (Pairwise.sublist (sublist_cons x xs) h)
    cases hP : p x with
    | true =>
      rw [Pairwise_cons] at h
      have : ∀ a ∈ xs, !p a := fun a hA => h.left a hA hP
      simp [eraseP, filter, hP, filter_eq_self.mpr this]
    | false => simp [eraseP_cons, filter, hP, ih]

theorem List.find?_eq_some {l : List α} {a : α} {p : α → Bool}
    : l.find? p = some a → a ∈ l ∧ p a := by
  induction l with
  | nil => intro h; cases h
  | cons x xs ih =>
    unfold find?
    cases hP : (p x)
    . intro h
      simp [List.mem_cons, ih h]
    . simp
      intro hEq
      simp [← hEq, hP]

/-- If there is at most one element with the property `p`, finding that one element is the same
as finding any. -/
theorem List.find?_eq_some_of_unique {l : List α} {a : α} {p : α → Bool}
    : l.Pairwise (p · → !p ·) → (l.find? p = some a ↔ (a ∈ l ∧ p a)) := by
  refine fun h => ⟨find?_eq_some, ?_⟩
  induction l with
  | nil => simp
  | cons x xs ih =>
    intro ⟨hMem, hP⟩
    cases List.mem_cons.mp hMem with
    | inl hX => simp [find?, ← hX, hP]
    | inr hXs =>
      unfold find?
      cases hPX : (p x) with
      | false =>
        apply ih (List.Pairwise.sublist (List.sublist_cons x xs) h) ⟨hXs, hP⟩
      | true =>
        cases hP ▸ (Pairwise_cons.mp h |>.left a hXs hPX)

@[simp]
theorem List.foldl_cons_fn (l₁ l₂ : List α) :
    l₁.foldl (init := l₂) (fun acc x => x :: acc) = l₁.reverse ++ l₂ := by
  induction l₁ generalizing l₂ <;> simp [*]

@[simp]
theorem List.foldl_append_fn (l₁ : List α) (l₂ : List β) (f : α → List β) :
    l₁.foldl (init := l₂) (fun acc x => acc ++ f x) = l₂ ++ l₁.bind f := by
  induction l₁ generalizing l₂ <;> simp [*]

theorem Array.exists_get_of_mem_data {as : Array α} {a : α}
    : a ∈ as.data → ∃ (i : Fin as.size), a = as[i] := by
  rw [← Array.toList_eq, Array.toList]
  apply Array.foldr_induction
    (motive := fun _ acc => a ∈ acc → ∃ (i : Fin as.size), a = as[i])
  case h0 => intro h; cases h
  case hf =>
    intro i acc ih h
    cases List.mem_cons.mp h with
    | inl h => exact ⟨i, h⟩
    | inr h => exact ih h

namespace Std.HashMap
open List

variable [BEq α] [Hashable α] [LawfulHashable α] [PartialEquivBEq α]

-- NOTE(WN): These would ideally be solved by a congruence-closure-for-PERs tactic
-- See https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/Rewriting.20congruent.20relations
private theorem beq_nonsense_1 {a b c : α} : a != b → a == c → b != c :=
  fun h₁ h₂ => Bool.bne_iff_not_beq.mpr fun h₃ =>
    Bool.bne_iff_not_beq.mp h₁ (PartialEquivBEq.trans h₂ (PartialEquivBEq.symm h₃))

private theorem beq_nonsense_2 {a b c : α} : a == b → b == c → ¬(c != a) :=
  fun h₁ h₂ h₃ => Bool.bne_iff_not_beq.mp (bne_symm h₃) (PartialEquivBEq.trans h₁ h₂)

/-- It is a bit easier to reason about `foldl (append)` than `foldl (foldl)`, so we use this
(less efficient) variant of `toList` as the mathematical model. -/
def toListModel (m : HashMap α β) : List (α × β) :=
  m.val.buckets.val.foldl (init := []) (fun acc bkt => acc ++ bkt.toList)

theorem toList_eq_reverse_toListModel (m : HashMap α β) : m.toList = m.toListModel.reverse := by
  simp only [toList, toListModel, fold, Imp.fold, Array.foldl_eq_foldl_data, AssocList.foldl_eq,
    List.foldl_cons_fn]
  suffices ∀ (l₁ : List (AssocList α β)) (l₂ : List (α × β)),
      l₁.foldl (init := l₂.reverse) (fun d b => b.toList.reverse ++ d) =
      (l₁.foldl (init := l₂) fun acc bkt => acc ++ bkt.toList).reverse by
    apply this (l₂ := [])
  intro l₁
  induction l₁ with
  | nil => intro; rfl
  | cons a as ih =>
    intro l₂
    simp only [List.foldl, ← List.reverse_append, ih]

/-- The contents of any given bucket are pairwise `bne`. -/
theorem Pairwise_bne_bucket (m : HashMap α β) (i : Fin m.val.buckets.val.size) :
  Pairwise (·.1 != ·.1) m.val.buckets.val[i].toList := by
  have hWF := Imp.WF_iff.mp m.property |>.right
  have := hWF.distinct m.val.buckets.val[i] (Array.getElem_mem_data _ _)
  exact List.Pairwise.imp Bool.bne_iff_not_beq.mpr this

/-- The map does not store duplicate (by `beq`) keys. -/
theorem Pairwise_bne_toListModel (m : HashMap α β) : m.toListModel.Pairwise (·.1 != ·.1) := by
  unfold toListModel
  refine Array.foldl_induction
    (motive := fun i (acc : List (α × β)) =>
      -- The acc has the desired property
      acc.Pairwise (·.1 != ·.1)
      -- All not-yet-accumulated buckets are pairwise disjoint with the acc
      ∧ ∀ j, i ≤ j → (_ : j < m.val.buckets.val.size) →
        ∀ p ∈ acc, ∀ r ∈ m.val.buckets.val[j].toList, p.1 != r.1)
    ?h0 ?hf |>.left
  case h0 => exact ⟨List.Pairwise.nil, fun.⟩
  case hf =>
    have hWF := Imp.WF_iff.mp m.property |>.right
    intro i acc h
    refine ⟨List.pairwise_append.mpr ⟨h.left, ?bkt, ?accbkt⟩, ?accbkts⟩
    case bkt => apply Pairwise_bne_bucket
    case accbkt =>
      intro a hA b hB
      exact h.right i.val (Nat.le_refl _) i.isLt a hA b hB
    case accbkts =>
      intro j hGe hLt p hP r hR
      cases List.mem_append.mp hP
      case inl hP => exact h.right j (Nat.le_of_succ_le hGe) hLt p hP r hR
      case inr hP =>
        -- Main proof 2: distinct buckets store bne keys
        refine Bool.bne_iff_not_beq.mpr fun h => ?_
        have hHashEq := LawfulHashable.hash_eq h
        have hGt := Nat.lt_of_succ_le hGe
        have hHashP := hWF.hash_self i (Nat.lt_trans hGt hLt) _ hP
        have hHashR := hWF.hash_self j hLt _ hR
        dsimp at hHashP hHashR
        have : i.val = j := by
          rw [hHashEq] at hHashP
          exact .trans hHashP.symm hHashR
        exact Nat.ne_of_lt hGt this

theorem toListModel_eraseP_eq_toListModel_filter (m : HashMap α β)
    : m.toListModel.eraseP (·.1 == a) = m.toListModel.filter (·.1 != a) := by
  apply List.eraseP_eq_filter_of_unique
  apply List.Pairwise.imp ?_ (Pairwise_bne_toListModel _)
  intro (a₁, _) (a₂, _) hA₁Bne hA₁Beq
  rw [Bool.not_eq_true_iff_ne_true, ← Bool.bne_iff_not_beq]
  exact beq_nonsense_1 hA₁Bne hA₁Beq

theorem mem_toListModel_iff_mem_bucket (m : HashMap α β) (a : α) (b : β)
    : haveI := Imp.mkIdx m.val.buckets.2 a
      (a, b) ∈ m.toListModel ↔ (a, b) ∈ (m.val.buckets.val[this.1]'this.2).toList := by
  have : (a, b) ∈ m.toListModel ↔ ∃ bkt ∈ m.val.buckets.val.data, (a, b) ∈ bkt.toList := by
    simp [toListModel, Array.foldl_eq_foldl_data, List.foldl_append_fn, List.nil_append,
      List.mem_bind]
  rw [this]
  clear this
  apply Iff.intro
  . intro ⟨bkt, hBkt, hMem⟩
    have ⟨i, hGetI⟩ := Array.exists_get_of_mem_data hBkt
    simp only [getElem_fin] at hGetI
    suffices (Imp.mkIdx m.val.buckets.2 a).val.toNat = i by
      simp [Array.ugetElem_eq_getElem, this, ← hGetI, hMem]
    unfold Imp.mkIdx
    dsimp
    exact Imp.WF_iff.mp m.property |>.right |>.hash_self i.val i.isLt (a, b) (hGetI ▸ hMem)
  . intro h
    refine ⟨_, Array.getElem_mem_data _ _, h⟩

theorem findEntry?_eq (m : HashMap α β) (a : α)
    : m.findEntry? a = m.toListModel.find? (·.1 == a) := by
  have hPairwiseM : Pairwise (fun p q => p.1 == a → q.1 != a) m.toListModel :=
    Pairwise.imp (fun p q => beq_nonsense_1 p q) (Pairwise_bne_toListModel m)
  have hPairwiseBkt :
      haveI := Imp.mkIdx m.val.buckets.property a
      Pairwise (fun p q => p.1 == a → q.1 != a) (m.val.buckets.val[this.1]'this.2).toList := by
    sorry
  apply Option.ext
  intro (a', b)
  simp only [Option.mem_def, findEntry?, Imp.findEntry?, AssocList.findEntry?_eq,
    List.find?_eq_some_of_unique hPairwiseM, List.find?_eq_some_of_unique hPairwiseBkt,
    and_congr_left_iff]
  intro hBeq
  have : hash a' = hash a := LawfulHashable.hash_eq hBeq
  simp [mem_toListModel_iff_mem_bucket, Imp.mkIdx, this]

theorem findEntry?_eq_some (m : HashMap α β) (a : α) (b : β)
    : m.findEntry? a = some (a, b) ↔ (∃ a', a == a' ∧ (a', b) ∈ m.toListModel) := by
  sorry

theorem find?_eq (m : HashMap α β) (a : α)
    : m.find? a = (m.findEntry? a).map (·.2) := by
  sorry

theorem toListModel_insert_perm_cons_eraseP (m : HashMap α β) (a : α) (b : β)
    : (m.insert a b).toListModel ~ (a, b) :: m.toListModel.eraseP (·.1 == a) :=
  sorry

theorem toListModel_insert (m : HashMap α β) (a : α) (b : β)
    : (m.insert a b).toListModel ~ (a, b) :: m.toListModel.filter (·.1 != a) :=
  toListModel_eraseP_eq_toListModel_filter m ▸ toListModel_insert_perm_cons_eraseP m a b

theorem toListModel_erase_perm_eraseP (m : HashMap α β) (a : α)
    : (m.erase a).toListModel ~ m.toListModel.eraseP (·.1 == a) :=
  sorry

theorem toListModel_erase (m : HashMap α β) (a : α)
    : (m.erase a).toListModel ~ m.toListModel.filter (·.1 != a) :=
  toListModel_eraseP_eq_toListModel_filter m ▸ toListModel_erase_perm_eraseP m a

theorem find?_of_toListModel_not_contains (m : HashMap α β) (a : α)
    : (∀ a' (b : β), a == a' → (a', b) ∉ m.toListModel) ↔ m.find? a = none := by
  apply Iff.intro
  . rw [← Option.not_isSome_iff_eq_none]
    intro h hSome
    let ⟨b, hB⟩ := Option.isSome_iff_exists.mp hSome
    let ⟨a', hA, hMem⟩ := find?_of_toListModel_contains m a b |>.mpr hB
    exact h a' b hA hMem
  . intro h a' b hA hMem
    refine Option.ne_none_iff_exists.mpr ?_ h
    exact ⟨b, find?_of_toListModel_contains m a b |>.mp ⟨a', hA, hMem⟩ |>.symm⟩

theorem find?_insert (m : HashMap α β) (a a' b)
    : a' == a → (m.insert a b).find? a' = some b := by
  intro hEq
  apply (find?_of_toListModel_contains _ _ _).mp
  refine ⟨a, hEq, ?_⟩
  rw [List.Perm.mem_iff (toListModel_insert m a b)]
  apply List.mem_cons_self

theorem find?_insert_of_ne (m : HashMap α β) (a a' : α) (b : β)
    : a != a' → (m.insert a b).find? a' = m.find? a' := by
  intro hNe
  apply Option.ext
  intro b'
  show find? (insert m a b) a' = some b' ↔ find? m a' = some b'
  simp only [← find?_of_toListModel_contains, List.Perm.mem_iff (toListModel_insert m a b),
    List.mem_cons, List.mem_filter, Prod.mk.injEq]
  apply Iff.intro
  . intro ⟨a'', hA', h⟩
    cases h with
    | inl hEq =>
      cases hEq.left
      exfalso
      exact Bool.not_bne_of_beq (PartialEquivBEq.symm hA') hNe
    | inr hMem => exact ⟨a'', hA', hMem.left⟩
  . intro ⟨a'', hA', hMem⟩
    refine ⟨a'', hA', .inr ?_⟩
    refine ⟨hMem, Bool.not_eq_true_iff_ne_true.mpr ?_⟩
    intro hA''
    exact Bool.not_bne_of_beq (PartialEquivBEq.symm (PartialEquivBEq.trans hA' hA'')) hNe

theorem find?_erase (m : HashMap α β) (a a')
    : a == a' → (m.erase a).find? a' = none := by
  intro hEq
  apply (find?_of_toListModel_not_contains _ _).mp
  intro a₂ b hA₂ hMem
  rw [List.Perm.mem_iff (toListModel_erase m a)] at hMem
  have := List.mem_filter.mp hMem |>.right
  exact beq_nonsense_2 hEq hA₂ this

end Std.HashMap

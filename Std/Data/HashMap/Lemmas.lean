/-
Copyright (c) 2022-2023 Wojciech Nawrocki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Nawrocki
-/

import Std.Data.HashMap.Basic
import Std.Data.HashMap.WF
import Std.Data.List.Lemmas
import Std.Data.List.Perm
import Std.Data.List.AtMostOne
import Std.Data.Array.Lemmas

namespace Std.HashMap
variable [BEq α] [Hashable α] [LawfulHashable α] [PartialEquivBEq α]

namespace Imp
open List

-- NOTE(WN): These would ideally be solved by a congruence-closure-for-PERs tactic
-- See https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/Rewriting.20congruent.20relations
-- Same for proofs about List.Perm
private theorem beq_nonsense_1 {a b c : α} : a != b → a == c → b != c :=
  fun h₁ h₂ => bne_trans_left (bne_symm h₁) h₂

private theorem beq_nonsense_3 {a b c : α} : a != b → c == b → c != a :=
  fun h₁ h₂ => bne_trans_right h₂ (bne_symm h₁)

namespace Buckets

/-! ## Basic lemmas about the mathematical model -/

/-- The mathematical model of the bucket array is a list of (key, value) pairs.

We use this instead of `HashMap.toList`
because it's easier to reason about `foldl (append)`
than about `foldl (foldl)`.

We use `bkts.val.foldl` rather than `bkts.val.data.foldl`
because we sometimes need to reason about array indices. -/
noncomputable def toListModel (bkts : Buckets α β) : List (α × β) :=
  bkts.val.foldl (init := []) (fun acc bkt => acc ++ bkt.toList)

attribute [local simp] foldl_cons_fn foldl_append_fn

theorem toListModel_eq (bkts : Buckets α β) : bkts.toListModel = bkts.val.data.bind (·.toList) := by
  simp [toListModel, Array.foldl_eq_foldl_data]

/-- A (key, value) pair is in the list iff it's in the correct hash-determined bucket. -/
theorem mem_toListModel_iff_mem_bucket (bkts : Buckets α β) (H : bkts.WF) (ab : α × β) :
    haveI := mkIdx (hash ab.fst) bkts.property
    ab ∈ bkts.toListModel ↔ ab ∈ (bkts.val[this.1.toNat]'this.2).toList := by
  have : ab ∈ bkts.toListModel ↔ ∃ bkt ∈ bkts.val.data, ab ∈ bkt.toList := by
    simp [toListModel_eq, mem_bind]
  rw [this]
  clear this
  apply Iff.intro
  . intro ⟨bkt, hBkt, hMem⟩
    have ⟨i, hGetI⟩ := Array.get_of_mem_data hBkt
    simp only [getElem_fin] at hGetI
    suffices (mkIdx (hash ab.fst) bkts.property).val.toNat = i by
      simp [Array.ugetElem_eq_getElem, this, hGetI, hMem]
    unfold Imp.mkIdx
    dsimp
    exact H.hash_self i.val i.isLt ab (hGetI ▸ hMem)
  . intro h
    refine ⟨_, Array.getElem_mem_data _ _, h⟩

theorem exists_of_toListModel_update (bkts : Buckets α β) (i d h) :
    ∃ l₁ l₂, bkts.toListModel = l₁ ++ bkts.1[i.toNat].toList ++ l₂
      ∧ (bkts.update i d h).toListModel = l₁ ++ d.toList ++ l₂ := by
  have ⟨bs₁, bs₂, hTgt, _, hUpd⟩ := bkts.exists_of_update i d h
  refine ⟨bs₁.bind (·.toList), bs₂.bind (·.toList), ?_, ?_⟩
  . simp [toListModel_eq, hTgt]
  . simp [toListModel_eq, hUpd]

theorem exists_of_toListModel_update_WF (bkts : Buckets α β) (H : bkts.WF) (i d h) :
    ∃ l₁ l₂, bkts.toListModel = l₁ ++ bkts.1[i.toNat].toList ++ l₂
      ∧ (bkts.update i d h).toListModel = l₁ ++ d.toList ++ l₂
      ∧ ∀ ab ∈ l₁, ((hash ab.fst).toUSize % bkts.val.size) < i := by
  have ⟨bs₁, bs₂, hTgt, hLen, hUpd⟩ := bkts.exists_of_update i d h
  refine ⟨bs₁.bind (·.toList), bs₂.bind (·.toList), ?_, ?_, ?_⟩
  . simp [toListModel_eq, hTgt]
  . simp [toListModel_eq, hUpd]
  . intro ab hMem
    have ⟨bkt, hBkt, hAb⟩ := mem_bind.mp hMem
    clear hMem
    have ⟨⟨j, hJ⟩, hEq⟩ := get_of_mem hBkt
    have hJ' : j < bkts.val.size := by
      apply Nat.lt_trans hJ
      simp [Array.size, hTgt, Nat.lt_add_of_pos_right (Nat.succ_pos _)]
    have : ab ∈ (bkts.val[j]).toList := by
      suffices bkt = bkts.val[j] by rwa [this] at hAb
      have := @List.get_append _ _ (bkts.val[i] :: bs₂) j hJ
      dsimp at this
      rw [← hEq, ← this, ← get_of_eq hTgt ⟨j, _⟩]
      rfl
    rwa [hLen, ← H.hash_self _ _ _ this] at hJ

/-! ## Uniqueness of keys -/

/-- The contents of any given bucket are pairwise `bne`. -/
theorem Pairwise_bne_bucket (bkts : Buckets α β) (H : bkts.WF) (h : i < bkts.val.size) :
    Pairwise (·.1 != ·.1) bkts.val[i].toList := by
  have := H.distinct bkts.val[i] (Array.getElem_mem_data _ _)
  exact Pairwise.imp Bool.bne_iff_not_beq.mpr this

theorem atMostOne_beq_bucket (bkts : Buckets α β) (H : bkts.WF) (h : i < bkts.val.size) (a : α) :
    AtMostOne (·.1 == a) bkts.val[i].toList :=
  Pairwise.imp (fun h h₁ => by
    rw [Bool.not_eq_true]
    exact Bool.beq_eq_false_iff.mpr <| bne_trans_left (bne_symm h) h₁)
  (Pairwise_bne_bucket bkts H h)

/-- The map does not store duplicate (by `beq`) keys. -/
theorem Pairwise_bne_toListModel (bkts : Buckets α β) (H : bkts.WF) :
    bkts.toListModel.Pairwise (·.1 != ·.1) := by
  unfold toListModel
  refine Array.foldl_induction
    (motive := fun i (acc : List (α × β)) =>
      -- The acc has the desired property
      acc.Pairwise (·.1 != ·.1)
      -- All not-yet-accumulated buckets are pairwise disjoint with the acc
      ∧ ∀ j, i ≤ j → (_ : j < bkts.val.size) →
        ∀ p ∈ acc, ∀ r ∈ bkts.val[j].toList, p.1 != r.1)
    ?h0 ?hf |>.left
  case h0 => exact ⟨Pairwise.nil, fun.⟩
  case hf =>
    intro i acc h
    refine ⟨pairwise_append.mpr ⟨h.left, ?bkt, ?accbkt⟩, ?accbkts⟩
    case bkt => apply Pairwise_bne_bucket bkts H
    case accbkt =>
      intro a hA b hB
      exact h.right i.val (Nat.le_refl _) i.isLt a hA b hB
    case accbkts =>
      intro j hGe hLt p hP r hR
      cases mem_append.mp hP
      case inl hP => exact h.right j (Nat.le_of_succ_le hGe) hLt p hP r hR
      case inr hP =>
        -- Main proof 2: distinct buckets store bne keys
        refine Bool.bne_iff_not_beq.mpr fun h => ?_
        have hHashEq := LawfulHashable.hash_eq h
        have hGt := Nat.lt_of_succ_le hGe
        have hHashP := H.hash_self i (Nat.lt_trans hGt hLt) _ hP
        have hHashR := H.hash_self j hLt _ hR
        dsimp at hHashP hHashR
        have : i.val = j := by
          rw [hHashEq] at hHashP
          exact .trans hHashP.symm hHashR
        exact Nat.ne_of_lt hGt this

theorem atMostOne_beq_toListModel (bkts : Buckets α β) (H : bkts.WF) (a : α) :
    bkts.toListModel.AtMostOne (·.1 == a) :=
  Pairwise.imp
    (fun h h₁ => by
      rw [Bool.not_eq_true, Bool.beq_eq_false_iff]
      exact bne_trans_left (bne_symm h) h₁)
    (Pairwise_bne_toListModel bkts H)

/-! ## Commuting `toListModel` past map operations -/

@[simp]
theorem toListModel_mk (size : Nat) (h : size.isPowerOfTwo) :
    (Buckets.mk (α := α) (β := β) size h).toListModel = [] := by
  simp only [Buckets.mk, toListModel_eq, mkArray_data]
  clear h
  induction size <;> simp [*]

theorem toListModel_reinsertAux (tgt : Buckets α β) (a : α) (b : β) :
    (reinsertAux tgt a b).toListModel ~ (a, b) :: tgt.toListModel := by
  unfold reinsertAux
  have ⟨l₁, l₂, hTgt, hUpd⟩ :=
    haveI := mkIdx (hash a) tgt.property
    tgt.exists_of_toListModel_update this.1 (.cons a b (tgt.1[this.1.toNat]'this.2)) this.2
  simp [hTgt, hUpd, perm_middle]

theorem toListModel_foldl_reinsertAux (bkt : List (α × β)) (tgt : Buckets α β) :
    (bkt.foldl (init := tgt) fun acc x => reinsertAux acc x.fst x.snd).toListModel
    ~ tgt.toListModel ++ bkt := by
  induction bkt generalizing tgt with
  | nil => simp [Perm.refl]
  | cons p ps ih =>
    refine Perm.trans (ih _) ?_
    refine Perm.trans (Perm.append_right ps (toListModel_reinsertAux _ _ _)) ?_
    rw [cons_append]
    refine Perm.trans (Perm.symm perm_middle) ?_
    apply Perm.append_left _ (Perm.refl _)

theorem toListModel_expand (size : Nat) (bkts : Buckets α β) :
    (expand size bkts).buckets.toListModel ~ bkts.toListModel := by
  refine (go _ _ _).trans ?_
  rw [toListModel_mk, toListModel_eq]
  simp [Perm.refl]
where
  go (i : Nat) (src : Array (AssocList α β)) (target : Buckets α β) :
      (expand.go i src target).toListModel
      ~ (src.data.drop i).foldl (init := target.toListModel) (fun a b => a ++ b.toList) := by
    unfold expand.go; split
    case inl hI =>
      refine (go (i +1) _ _).trans ?_
      have h₀ : (src.data.set i AssocList.nil).drop (i + 1) = src.data.drop (i + 1) := by
        apply drop_ext
        intro j hJ
        apply get?_set_ne _ _ (Nat.ne_of_lt <| Nat.lt_of_succ_le hJ)
      have h₁ : (drop i src.data).bind (·.toList) = src.data[i].toList
          ++ (drop (i + 1) src.data).bind (·.toList) := by
        have : i < src.data.length := by simp [hI]
        simp [drop_eq_get_cons this]
      simp [h₀, h₁]
      rw [← append_assoc]
      refine Perm.append ?_ (Perm.refl _)
      refine Perm.trans (toListModel_foldl_reinsertAux (AssocList.toList src[i]) _) ?_
      exact Perm.refl _
    case inr hI =>
      have : src.data.length ≤ i := by simp [Nat.le_of_not_lt, hI]
      simp [Perm.refl, drop_eq_nil_of_le this]
    termination_by _ i src _ => src.size - i

end Buckets

/-! ## Map operations expressed in terms of `toListModel` -/

theorem findEntry?_eq (m : Imp α β) (H : m.buckets.WF) (a : α)
    : m.findEntry? a = m.buckets.toListModel.find? (·.1 == a) := by
  have hPairwiseBkt :
      haveI := mkIdx (hash a) m.buckets.property
      AtMostOne (·.1 == a) (m.buckets.val[this.1]'this.2).toList :=
    by apply Buckets.atMostOne_beq_bucket m.buckets H
  apply Option.ext
  intro (a', b)
  simp only [Option.mem_def, findEntry?, Imp.findEntry?, AssocList.findEntry?_eq,
    hPairwiseBkt.find?_eq_some_iff,
    (Buckets.atMostOne_beq_toListModel m.buckets H a).find?_eq_some_iff,
    and_congr_left_iff]
  intro hBeq
  have : hash a' = hash a := LawfulHashable.hash_eq hBeq
  simp [Buckets.mem_toListModel_iff_mem_bucket m.buckets H, mkIdx, this]

theorem eraseP_toListModel_of_not_contains (m : Imp α β) (H : m.buckets.WF) (a : α) :
    haveI := mkIdx (hash a) m.buckets.property
    ¬(m.buckets.val[this.1.toNat]'this.2).contains a →
    m.buckets.toListModel.eraseP (·.1 == a) = m.buckets.toListModel := by
  intro hContains
  apply eraseP_of_forall_not
  intro ab hMem hEq
  have :
      haveI := mkIdx (hash a) m.buckets.property
      (m.buckets.val[this.1.toNat]'this.2).contains a := by
    simp only [AssocList.contains_eq, List.any_eq_true, mkIdx, ← LawfulHashable.hash_eq hEq]
    exact ⟨ab, (Buckets.mem_toListModel_iff_mem_bucket m.buckets H ab).mp hMem, hEq⟩
  contradiction

theorem toListModel_insert_perm (m : Imp α β) (H : m.buckets.WF) (a : α) (b : β) :
    (m.insert a b).buckets.toListModel ~ (a, b) :: m.buckets.toListModel.eraseP (·.1 == a) := by
  dsimp [insert, cond]; split
  next hContains =>
    have ⟨l₁, l₂, hTgt, hUpd, hProp⟩ :=
      haveI := mkIdx (hash a) m.buckets.property
      m.buckets.exists_of_toListModel_update_WF H this.1
        ((m.buckets.1[this.1.toNat]'this.2).replace a b) this.2
    rw [hUpd, hTgt]
    have hL₁ : ∀ ab ∈ l₁, ¬(ab.fst == a) := fun ab h hEq =>
      Nat.ne_of_lt (LawfulHashable.hash_eq hEq ▸ hProp ab h) rfl
    have ⟨p, hMem, hP⟩ := any_eq_true.mp (AssocList.contains_eq a _ ▸ hContains)
    simp [eraseP_append_right _ hL₁,
      eraseP_append_left (p := fun ab => ab.fst == a) hP _ hMem]
    -- begin cursed manual proofs
    refine Perm.trans ?_ perm_middle
    refine Perm.append (Perm.refl _) ?_
    rw [← cons_append]
    refine Perm.append ?_ (Perm.refl _)

    refine Perm.trans
      (AtMostOne.replaceF_perm
        (b := (a, b))
        (f := fun a_1 => bif a_1.fst == a then some (a, b) else none)
        (AtMostOne.imp
          (fun a' => by cases h : a'.fst == a <;> simp [h])
          (Buckets.atMostOne_beq_bucket m.buckets H _ a))
        hMem
        (by simp [hP]))
      ?_
    apply List.Perm.of_eq
    congr
    apply funext
    intro x
    cases h : x.fst == a <;> simp [h]
    -- end cursed manual proofs

  next hContains =>
    rw [eraseP_toListModel_of_not_contains m H a (Bool.eq_false_iff.mp hContains)]
    split
    -- TODO(WN): how to merge the two branches below? They are identical except for the initial
    -- `refine`
    next =>
      have ⟨l₁, l₂, hTgt, hUpd⟩ :=
        haveI := mkIdx (hash a) m.buckets.property
        m.buckets.exists_of_toListModel_update this.1
          ((m.buckets.1[this.1.toNat]'this.2).cons a b) this.2
      simp [hTgt, hUpd, perm_middle]
    next =>
      refine Perm.trans (Buckets.toListModel_expand _ _) ?_
      have ⟨l₁, l₂, hTgt, hUpd⟩ :=
        haveI := mkIdx (hash a) m.buckets.property
        m.buckets.exists_of_toListModel_update this.1
          ((m.buckets.1[this.1.toNat]'this.2).cons a b) this.2
      simp [hTgt, hUpd, perm_middle]

theorem toListModel_erase (m : Imp α β) (H : m.buckets.WF) (a : α) :
    (m.erase a).buckets.toListModel = m.buckets.toListModel.eraseP (·.1 == a) := by
  dsimp [erase, cond]; split
  next hContains =>
    have ⟨l₁, l₂, hTgt, hUpd, hProp⟩ :=
      haveI := mkIdx (hash a) m.buckets.property
      m.buckets.exists_of_toListModel_update_WF H this.1
        ((m.buckets.1[this.1.toNat]'this.2).erase a) this.2
    rw [hTgt, hUpd]
    have hL₁ : ∀ ab ∈ l₁, ¬(ab.fst == a) := fun ab h hEq =>
      Nat.ne_of_lt (LawfulHashable.hash_eq hEq ▸ hProp ab h) rfl
    have ⟨p, hMem, hP⟩ := any_eq_true.mp (AssocList.contains_eq a _ ▸ hContains)
    simp [eraseP_append_right _ hL₁, eraseP_append_left (p := fun ab => ab.fst == a) hP _ hMem]
  next hContains =>
    rw [eraseP_toListModel_of_not_contains m H a (Bool.eq_false_iff.mp hContains)]

theorem eraseP_toListModel (m : Imp α β) (H : m.buckets.WF) (a : α) :
    m.buckets.toListModel.eraseP (·.1 == a) = m.buckets.toListModel.filter (·.1 != a) := by
  apply AtMostOne.eraseP_eq_filter
  apply Buckets.atMostOne_beq_toListModel m.buckets H

theorem toListModel_insert_perm' (m : Imp α β) (H : m.buckets.WF) (a : α) (b : β) :
    (m.insert a b).buckets.toListModel ~ (a, b) :: m.buckets.toListModel.filter (·.1 != a) :=
  eraseP_toListModel m H a ▸ toListModel_insert_perm m H a b

theorem toListModel_erase' (m : Imp α β) (H : m.buckets.WF) (a : α) :
    (m.erase a).buckets.toListModel = m.buckets.toListModel.filter (·.1 != a) :=
  eraseP_toListModel m H a ▸ toListModel_erase m H a

end Std.HashMap.Imp

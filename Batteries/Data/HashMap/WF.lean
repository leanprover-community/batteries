/-
Copyright (c) 2022 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Batteries.Tactic.SeqFocus
import Batteries.Data.HashMap.Basic
import Batteries.Data.Nat.Lemmas
import Batteries.Data.List.Lemmas

namespace Batteries.HashMap
namespace Imp

attribute [-simp] Bool.not_eq_true

namespace Buckets

@[ext] protected theorem ext : ∀ {b₁ b₂ : Buckets α β}, b₁.1.data = b₂.1.data → b₁ = b₂
  | ⟨⟨_⟩, _⟩, ⟨⟨_⟩, _⟩, rfl => rfl

theorem update_data (self : Buckets α β) (i d h) :
    (self.update i d h).1.data = self.1.data.set i.toNat d := rfl

theorem exists_of_update (self : Buckets α β) (i d h) :
    ∃ l₁ l₂, self.1.data = l₁ ++ self.1[i] :: l₂ ∧ List.length l₁ = i.toNat ∧
      (self.update i d h).1.data = l₁ ++ d :: l₂ := by
  simp only [Array.data_length, Array.ugetElem_eq_getElem, Array.getElem_eq_data_getElem]
  exact List.exists_of_set h

theorem update_update (self : Buckets α β) (i d d' h h') :
    (self.update i d h).update i d' h' = self.update i d' h := by
  simp only [update, Array.uset, Array.data_length]
  congr 1
  rw [Array.set_set]

theorem size_eq (data : Buckets α β) :
  size data = .sum (data.1.data.map (·.toList.length)) := rfl

theorem mk_size (h) : (mk n h : Buckets α β).size = 0 := by
  simp only [mk, mkArray, size_eq]; clear h
  induction n <;> simp_all [List.replicate_succ]

theorem WF.mk' [BEq α] [Hashable α] (h) : (Buckets.mk n h : Buckets α β).WF := by
  refine ⟨fun _ h => ?_, fun i h => ?_⟩
  · simp only [Buckets.mk, mkArray, List.mem_replicate, ne_eq] at h
    simp [h, List.Pairwise.nil]
  · simp [Buckets.mk, empty', mkArray, Array.getElem_eq_data_getElem, AssocList.All]

theorem WF.update [BEq α] [Hashable α] {buckets : Buckets α β} {i d h} (H : buckets.WF)
    (h₁ : ∀ [PartialEquivBEq α] [LawfulHashable α],
      (buckets.1[i].toList.Pairwise fun a b => ¬(a.1 == b.1)) →
      d.toList.Pairwise fun a b => ¬(a.1 == b.1))
    (h₂ : (buckets.1[i].All fun k _ => ((hash k).toUSize % buckets.1.size).toNat = i.toNat) →
      d.All fun k _ => ((hash k).toUSize % buckets.1.size).toNat = i.toNat) :
    (buckets.update i d h).WF := by
  refine ⟨fun l hl => ?_, fun i hi p hp => ?_⟩
  · exact match List.mem_or_eq_of_mem_set hl with
    | .inl hl => H.1 _ hl
    | .inr rfl => h₁ (H.1 _ (Array.getElem_mem_data ..))
  · revert hp
    simp only [Array.getElem_eq_data_getElem, update_data, List.getElem_set, Array.data_length,
      update_size]
    split <;> intro hp
    · next eq => exact eq ▸ h₂ (H.2 _ _) _ hp
    · simp only [update_size, Array.data_length] at hi
      exact H.2 i hi _ hp

end Buckets

theorem reinsertAux_size [Hashable α] (data : Buckets α β) (a : α) (b : β) :
    (reinsertAux data a b).size = data.size.succ := by
  simp only [reinsertAux, Array.data_length, Array.ugetElem_eq_getElem, Buckets.size_eq,
    Nat.succ_eq_add_one]
  refine have ⟨l₁, l₂, h₁, _, eq⟩ := Buckets.exists_of_update ..; eq ▸ ?_
  simp [h₁, Nat.succ_add]; rfl

theorem reinsertAux_WF [BEq α] [Hashable α] {data : Buckets α β} {a : α} {b : β} (H : data.WF)
    (h₁ : ∀ [PartialEquivBEq α] [LawfulHashable α],
      haveI := mkIdx data.2 (hash a).toUSize
      data.val[this.1].All fun x _ => ¬(a == x)) :
    (reinsertAux data a b).WF :=
  H.update (.cons h₁) fun
    | _, _, .head .. => rfl
    | H, _, .tail _ h => H _ h

theorem expand_size [Hashable α] {buckets : Buckets α β} :
    (expand sz buckets).buckets.size = buckets.size := by
  rw [expand, go]
  · rw [Buckets.mk_size]; simp [Buckets.size]
  · nofun
where
  go (i source) (target : Buckets α β) (hs : ∀ j < i, source.data[j]?.getD .nil = .nil) :
      (expand.go i source target).size =
        .sum (source.data.map (·.toList.length)) + target.size := by
    unfold expand.go; split
    · next H =>
      refine (go (i+1) _ _ fun j hj => ?a).trans ?b <;> simp
      · case a =>
        simp [List.getD_eq_getElem?_getD, List.getElem?_set, Option.map_eq_map]; split
        · cases source.data[j]? <;> rfl
        · next H => exact hs _ (Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hj) (Ne.symm H))
      · case b =>
        refine have ⟨l₁, l₂, h₁, _, eq⟩ := List.exists_of_set H; eq ▸ ?_
        rw [h₁]
        simp only [Buckets.size_eq, List.map_append, List.map_cons, AssocList.toList,
          List.length_nil, Nat.sum_append, Nat.sum_cons, Nat.zero_add, Array.data_length]
        rw [Nat.add_assoc, Nat.add_assoc, Nat.add_assoc]; congr 1
        (conv => rhs; rw [Nat.add_left_comm]); congr 1
        rw [← Array.getElem_eq_data_getElem]
        have := @reinsertAux_size α β _; simp [Buckets.size] at this
        induction source[i].toList generalizing target <;> simp [*, Nat.succ_add]; rfl
    · next H =>
      rw [(_ : Nat.sum _ = 0), Nat.zero_add]
      rw [← (_ : source.data.map (fun _ => .nil) = source.data)]
      · simp only [List.map_map]
        induction source.data <;> simp [*]
      refine List.ext_getElem (by simp) fun j h₁ h₂ => ?_
      simp only [List.getElem_map, Array.data_length]
      have := (hs j (Nat.lt_of_lt_of_le h₂ (Nat.not_lt.1 H))).symm
      rwa [List.getElem?_eq_getElem] at this
  termination_by source.size - i

theorem expand_WF.foldl [BEq α] [Hashable α] (rank : α → Nat) {l : List (α × β)} {i : Nat}
    (hl₁ : ∀ [PartialEquivBEq α] [LawfulHashable α], l.Pairwise fun a b => ¬(a.1 == b.1))
    (hl₂ : ∀ x ∈ l, rank x.1 = i)
    {target : Buckets α β} (ht₁ : target.WF)
    (ht₂ : ∀ bucket ∈ target.1.data,
      bucket.All fun k _ => rank k ≤ i ∧
        ∀ [PartialEquivBEq α] [LawfulHashable α], ∀ x ∈ l, ¬(x.1 == k)) :
    (l.foldl (fun d x => reinsertAux d x.1 x.2) target).WF ∧
    ∀ bucket ∈ (l.foldl (fun d x => reinsertAux d x.1 x.2) target).1.data,
      bucket.All fun k _ => rank k ≤ i := by
  induction l generalizing target with
  | nil => exact ⟨ht₁, fun _ h₁ _ h₂ => (ht₂ _ h₁ _ h₂).1⟩
  | cons _ _ ih =>
    simp only [List.pairwise_cons, List.mem_cons, forall_eq_or_imp] at hl₁ hl₂ ht₂
    refine ih hl₁.2 hl₂.2
      (reinsertAux_WF ht₁ fun _ h => (ht₂ _ (Array.getElem_mem_data ..) _ h).2.1)
      (fun _ h => ?_)
    simp only [reinsertAux, Buckets.update, Array.uset, Array.data_length,
      Array.ugetElem_eq_getElem, Array.data_set] at h
    match List.mem_or_eq_of_mem_set h with
    | .inl h =>
      intro _ hf
      have ⟨h₁, h₂⟩ := ht₂ _ h _ hf
      exact ⟨h₁, h₂.2⟩
    | .inr h => subst h; intro
      | _, .head .. =>
        exact ⟨hl₂.1 ▸ Nat.le_refl _, fun _ h h' => hl₁.1 _ h (PartialEquivBEq.symm h')⟩
      | _, .tail _ h =>
        have ⟨h₁, h₂⟩ := ht₂ _ (Array.getElem_mem_data ..) _ h
        exact ⟨h₁, h₂.2⟩

theorem expand_WF [BEq α] [Hashable α] {buckets : Buckets α β} (H : buckets.WF) :
    (expand sz buckets).buckets.WF :=
  go _ H.1 H.2 ⟨.mk' _, fun _ _ _ _ => by simp_all [Buckets.mk, List.mem_replicate]⟩
where
  go (i) {source : Array (AssocList α β)}
      (hs₁ : ∀ [LawfulHashable α] [PartialEquivBEq α], ∀ bucket ∈ source.data,
        bucket.toList.Pairwise fun a b => ¬(a.1 == b.1))
      (hs₂ : ∀ (j : Nat) (h : j < source.size),
        source[j].All fun k _ => ((hash k).toUSize % source.size).toNat = j)
      {target : Buckets α β} (ht : target.WF ∧ ∀ bucket ∈ target.1.data,
        bucket.All fun k _ => ((hash k).toUSize % source.size).toNat < i) :
      (expand.go i source target).WF := by
    unfold expand.go; split
    · next H =>
      refine go (i+1) (fun _ hl => ?_) (fun i h => ?_) ?_
      · match List.mem_or_eq_of_mem_set hl with
        | .inl hl => exact hs₁ _ hl
        | .inr e => exact e ▸ .nil
      · simp only [Array.data_length, Array.size_set, Array.getElem_eq_data_getElem, Array.data_set,
          List.getElem_set]
        split
        · nofun
        · exact hs₂ _ (by simp_all)
      · let rank (k : α) := ((hash k).toUSize % source.size).toNat
        have := expand_WF.foldl rank ?_ (hs₂ _ H) ht.1 (fun _ h₁ _ h₂ => ?_)
        · simp only [Array.get_eq_getElem, AssocList.foldl_eq, Array.size_set]
          exact ⟨this.1, fun _ h₁ _ h₂ => Nat.lt_succ_of_le (this.2 _ h₁ _ h₂)⟩
        · exact hs₁ _ (Array.getElem_mem_data ..)
        · have := ht.2 _ h₁ _ h₂
          refine ⟨Nat.le_of_lt this, fun _ h h' => Nat.ne_of_lt this ?_⟩
          exact LawfulHashable.hash_eq h' ▸ hs₂ _ H _ h
    · exact ht.1
  termination_by source.size - i

theorem insert_size [BEq α] [Hashable α] {m : Imp α β} {k v}
    (h : m.size = m.buckets.size) :
    (insert m k v).size = (insert m k v).buckets.size := by
  dsimp [insert, cond]; split
  · unfold Buckets.size
    refine have ⟨_, _, h₁, _, eq⟩ := Buckets.exists_of_update ..; eq ▸ ?_
    simp [h, h₁, Buckets.size_eq]
  split
  · unfold Buckets.size
    refine have ⟨_, _, h₁, _, eq⟩ := Buckets.exists_of_update ..; eq ▸ ?_
    simp [h, h₁, Buckets.size_eq, Nat.succ_add]; rfl
  · rw [expand_size]; simp only [expand, h, Buckets.size, Array.data_length, Buckets.update_size]
    refine have ⟨_, _, h₁, _, eq⟩ := Buckets.exists_of_update ..; eq ▸ ?_
    simp [h₁, Buckets.size_eq, Nat.succ_add]; rfl

private theorem mem_replaceF {l : List (α × β)} {x : α × β} {p : α × β → Bool} {f : α × β → β} :
    x ∈ (l.replaceF fun a => bif p a then some (k, f a) else none) → x.1 = k ∨ x ∈ l := by
  induction l with
  | nil => exact .inr
  | cons a l ih =>
    simp only [List.replaceF, List.mem_cons]
    generalize e : cond .. = z; revert e
    unfold cond; split <;> (intro h; subst h; simp)
    · intro
      | .inl eq => exact eq ▸ .inl rfl
      | .inr h => exact .inr (.inr h)
    · intro
      | .inl eq => exact .inr (.inl eq)
      | .inr h => exact (ih h).imp_right .inr

private theorem pairwise_replaceF [BEq α] [PartialEquivBEq α]
    {l : List (α × β)} {f : α × β → β}
    (H : l.Pairwise fun a b => ¬(a.fst == b.fst)) :
    (l.replaceF fun a => bif a.fst == k then some (k, f a) else none)
      |>.Pairwise fun a b => ¬(a.fst == b.fst) := by
  induction l with
  | nil => simp [H]
  | cons a l ih =>
    simp only [List.pairwise_cons, List.replaceF] at H ⊢
    generalize e : cond .. = z; unfold cond at e; revert e
    split <;> (intro h; subst h; simp only [List.pairwise_cons])
    · next e => exact ⟨(H.1 · · ∘ PartialEquivBEq.trans e), H.2⟩
    · next e =>
      refine ⟨fun a h => ?_, ih H.2⟩
      match mem_replaceF h with
      | .inl eq => exact eq ▸ ne_true_of_eq_false e
      | .inr h => exact H.1 a h

theorem insert_WF [BEq α] [Hashable α] {m : Imp α β} {k v}
    (h : m.buckets.WF) : (insert m k v).buckets.WF := by
  dsimp [insert, cond]; split
  · next h₁ =>
    simp only [AssocList.contains_eq, List.any_eq_true] at h₁; have ⟨x, hx₁, hx₂⟩ := h₁
    refine h.update (fun H => ?_) (fun H a h => ?_)
    · simp only [AssocList.toList_replace]
      exact pairwise_replaceF H
    · simp only [AssocList.All, Array.ugetElem_eq_getElem, AssocList.toList_replace] at H h ⊢
      match mem_replaceF h with
      | .inl rfl => rfl
      | .inr h => exact H _ h
  · next h₁ =>
    rw [Bool.eq_false_iff] at h₁
    simp only [AssocList.contains_eq, ne_eq, List.any_eq_true, not_exists, not_and] at h₁
    suffices _ by split <;> [exact this; refine expand_WF this]
    refine h.update (.cons ?_) (fun H a h => ?_)
    · exact fun a h h' => h₁ a h (PartialEquivBEq.symm h')
    · cases h with
      | head => rfl
      | tail _ h => exact H _ h

theorem erase_size [BEq α] [Hashable α] {m : Imp α β} {k}
    (h : m.size = m.buckets.size) :
    (erase m k).size = (erase m k).buckets.size := by
  dsimp [erase, cond]; split
  · next H =>
    simp only [h, Buckets.size]
    refine have ⟨_, _, h₁, _, eq⟩ := Buckets.exists_of_update ..; eq ▸ ?_
    simp only [h₁, Array.data_length, Array.ugetElem_eq_getElem, List.map_append, List.map_cons,
      Nat.sum_append, Nat.sum_cons, AssocList.toList_erase]
    rw [(_ : List.length _ = _ + 1), Nat.add_right_comm]; {rfl}
    clear h₁ eq
    simp only [AssocList.contains_eq, List.any_eq_true] at H
    have ⟨a, h₁, h₂⟩ := H
    refine have ⟨_, _, _, _, _, h, eq⟩ := List.exists_of_eraseP h₁ h₂; eq ▸ ?_
    simp [h]; rfl
  · exact h

theorem erase_WF [BEq α] [Hashable α] {m : Imp α β} {k}
    (h : m.buckets.WF) : (erase m k).buckets.WF := by
  dsimp [erase, cond]; split
  · refine h.update (fun H => ?_) (fun H a h => ?_) <;> simp only [AssocList.toList_erase] at h ⊢
    · exact H.sublist (List.eraseP_sublist _)
    · exact H _ (List.mem_of_mem_eraseP h)
  · exact h

theorem modify_size [BEq α] [Hashable α] {m : Imp α β} {k}
    (h : m.size = m.buckets.size) :
    (modify m k f).size = (modify m k f).buckets.size := by
  dsimp [modify, cond]; rw [Buckets.update_update]
  simp only [h, Buckets.size]
  refine have ⟨_, _, h₁, _, eq⟩ := Buckets.exists_of_update ..; eq ▸ ?_
  simp [h, h₁, Buckets.size_eq]

theorem modify_WF [BEq α] [Hashable α] {m : Imp α β} {k}
    (h : m.buckets.WF) : (modify m k f).buckets.WF := by
  dsimp [modify, cond]; rw [Buckets.update_update]
  refine h.update (fun H => ?_) (fun H a h => ?_) <;> simp at h ⊢
  · exact pairwise_replaceF H
  · simp only [AssocList.All, Array.ugetElem_eq_getElem] at H h ⊢
    match mem_replaceF h with
    | .inl rfl => rfl
    | .inr h => exact H _ h

theorem WF.out [BEq α] [Hashable α] {m : Imp α β} (h : m.WF) :
    m.size = m.buckets.size ∧ m.buckets.WF := by
  induction h with
  | mk h₁ h₂ => exact ⟨h₁, h₂⟩
  | @empty' _ h => exact ⟨(Buckets.mk_size h).symm, .mk' h⟩
  | insert _ ih => exact ⟨insert_size ih.1, insert_WF ih.2⟩
  | erase _ ih => exact ⟨erase_size ih.1, erase_WF ih.2⟩
  | modify _ ih => exact ⟨modify_size ih.1, modify_WF ih.2⟩

theorem WF_iff [BEq α] [Hashable α] {m : Imp α β} :
    m.WF ↔ m.size = m.buckets.size ∧ m.buckets.WF :=
  ⟨(·.out), fun ⟨h₁, h₂⟩ => .mk h₁ h₂⟩

theorem WF.mapVal {α β γ} {f : α → β → γ} [BEq α] [Hashable α]
    {m : Imp α β} (H : WF m) : WF (mapVal f m) := by
  have ⟨h₁, h₂⟩ := H.out
  simp only [Imp.mapVal, h₁, Buckets.mapVal, WF_iff]; refine ⟨?_, ?_, fun i h => ?_⟩
  · simp only [Buckets.size, Array.map_data, List.map_map]; congr; funext l; simp
  · simp only [Array.map_data, List.forall_mem_map]
    simp only [AssocList.toList_mapVal, List.pairwise_map]
    exact fun _ => h₂.1 _
  · simp only [Array.size_map, AssocList.All, Array.getElem_map, AssocList.toList_mapVal,
      List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂] at h ⊢
    intro a m
    apply h₂.2 _ _ _ m

theorem WF.filterMap {α β γ} {f : α → β → Option γ} [BEq α] [Hashable α]
    {m : Imp α β} (H : WF m) : WF (filterMap f m) := by
  let g₁ (l : AssocList α β) := l.toList.filterMap (fun x => (f x.1 x.2).map (x.1, ·))
  have H1 (l n acc) : filterMap.go f acc l n =
      (((g₁ l).reverse ++ acc.toList).toAssocList, ⟨n.1 + (g₁ l).length⟩) := by
    induction l generalizing n acc with simp only [filterMap.go, AssocList.toList,
      List.filterMap_nil, List.reverse_nil, List.nil_append, AssocList.toList_toAssocList,
      List.length_nil, Nat.add_zero, List.filterMap_cons, g₁, *]
    | cons a b l => match f a b with
      | none => rfl
      | some c =>
        simp only [Option.map_some', List.reverse_cons, List.append_assoc, List.singleton_append,
          List.length_cons, Nat.succ_eq_add_one, Prod.mk.injEq, true_and]
        rw [Nat.add_right_comm]
        rfl
  let g l := (g₁ l).reverse.toAssocList
  let M := StateT (ULift Nat) Id
  have H2 (l : List (AssocList α β)) n :
      l.mapM (m := M) (filterMap.go f .nil) n =
      (l.map g, ⟨n.1 + .sum ((l.map g).map (·.toList.length))⟩) := by
    induction l generalizing n with
    | nil => rfl
    | cons l L IH => simp [bind, StateT.bind, IH, H1, Nat.add_assoc, g]; rfl
  have H3 (l : List _) :
    (l.filterMap (fun (a, b) => (f a b).map (a, ·))).map (fun a => a.fst)
     |>.Sublist (l.map (·.1)) := by
    induction l with
    | nil => exact .slnil
    | cons a l ih =>
      simp only [List.filterMap_cons, List.map_cons]; exact match f a.1 a.2 with
      | none => .cons _ ih
      | some b => .cons₂ _ ih
  suffices ∀ bk sz (h : 0 < bk.length),
    m.buckets.val.mapM (m := M) (filterMap.go f .nil) ⟨0⟩ = (⟨bk⟩, ⟨sz⟩) →
    WF ⟨sz, ⟨bk⟩, h⟩ from this _ _ _ rfl
  simp only [Array.mapM_eq_mapM_data, bind, StateT.bind, H2, List.map_map, Nat.zero_add, g]
  intro bk sz h e'; cases e'
  refine .mk (by simp [Buckets.size]) ⟨?_, fun i h => ?_⟩
  · simp only [List.forall_mem_map, List.toList_toAssocList]
    refine fun l h => (List.pairwise_reverse.2 ?_).imp (mt PartialEquivBEq.symm)
    have := H.out.2.1 _ h
    rw [← List.pairwise_map (R := (¬ · == ·))] at this ⊢
    exact this.sublist (H3 l.toList)
  · simp only [Array.size_mk, List.length_map, Array.data_length, Array.getElem_eq_data_getElem,
      List.getElem_map] at h ⊢
    have := H.out.2.2 _ h
    simp only [AssocList.All, List.toList_toAssocList, List.mem_reverse, List.mem_filterMap,
      Option.map_eq_some', forall_exists_index, and_imp, g₁] at this ⊢
    rintro _ _ h' _ _ rfl
    exact this _ h'

end Imp

variable {_ : BEq α} {_ : Hashable α}

/-- Map a function over the values in the map. -/
@[inline] def mapVal (f : α → β → γ) (self : HashMap α β) : HashMap α γ :=
  ⟨self.1.mapVal f, self.2.mapVal⟩

/--
Applies `f` to each key-value pair `a, b` in the map. If it returns `some c` then
`a, c` is pushed into the new map; else the key is removed from the map.
-/
@[inline] def filterMap (f : α → β → Option γ) (self : HashMap α β) : HashMap α γ :=
  ⟨self.1.filterMap f, self.2.filterMap⟩

/-- Constructs a map with the set of all pairs `a, b` such that `f` returns true. -/
@[inline] def filter (f : α → β → Bool) (self : HashMap α β) : HashMap α β :=
  self.filterMap fun a b => bif f a b then some b else none

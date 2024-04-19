/-
Copyright (c) 2022 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Std.Data.HashMap.Basic
import Std.Data.List.Lemmas
import Std.Data.Array.Lemmas
import Std.Data.Nat.Lemmas

namespace Std.HashMap
namespace Imp

attribute [-simp] Bool.not_eq_true

namespace Buckets


@[ext] protected theorem ext : ∀ {b₁ b₂ : Buckets α β}, b₁.1.data = b₂.1.data → b₁ = b₂
  | ⟨⟨_⟩⟩, ⟨⟨_⟩⟩, rfl => rfl

theorem update_data (self : Buckets α β) (i d h) :
    (self.update i d h).1.data = self.1.data.set i.toNat d := rfl

theorem exists_of_update (self : Buckets α β) (i d h) :
    ∃ l₁ l₂, self.1.data = l₁ ++ self.1[i] :: l₂ ∧ List.length l₁ = i.toNat ∧
      (self.update i d h).1.data = l₁ ++ d :: l₂ := by
  simp [Array.getElem_eq_data_get]; exact List.exists_of_set' h

theorem update_update (self : Buckets α β) (i d d' h h') :
    (self.update i d h).update i d' h' = self.update i d' h := by
  simp [update]; rw [Array.set_set]

theorem size_eq (data : Buckets α β) :
  size data = .sum (data.1.data.map (·.toList.length)) := rfl

@[simp] theorem mk_size : (mk n : Buckets α β).size = 0 := by
  simp [Buckets.size_eq, Buckets.mk, mkArray]
  induction n <;> simp [*]

@[simp] theorem mk_size' : (mk n : Buckets α β).1.size = n := by
  simp [Buckets.mk]

theorem WF.mk' [BEq α] [Hashable α] (h : 0 < n) : (Buckets.mk n : Buckets α β).WF := by
  refine ⟨fun i h => ?_, fun i h => ?_, ?_⟩
  · simp [Buckets.mk]
  · simp [Buckets.mk, empty', mkArray, Array.getElem_eq_data_get, AssocList.All]
  · simpa [Buckets.mk]

theorem update_get (self : Buckets α β) (i d h) (j : Nat) (hj : j < (self.update i d h).1.size) :
    haveI : j < self.1.size := by simpa using hj
    (self.update i d h).1[j] = if i.toNat = j then d else self.1[j] := by
  simp [update_data, Array.getElem_eq_data_get, List.get_set]

-- Strategy: Get rid of weird (∈/access)-dichotomy -- why not use access anywhere?
-- Factor out BucketWFAt structure
-- Get contains-based
-- Do it like in my repo, except that WF is unbundled
-- Everyting EXCEPT expand should be easy now
-- Hopefully expand isn't harder? :/

theorem WF.update [BEq α] [Hashable α] {buckets : Buckets α β} {i d h} (H : buckets.WF)
    (h₁ : ∀ [PartialEquivBEq α] [LawfulHashable α],
      buckets.1[i].WF → d.WF)
    (h₂ : (buckets.1[i].All fun k _ => ((hash k).toUSize % buckets.1.size).toNat = i.toNat) →
      d.All fun k _ => ((hash k).toUSize % buckets.1.size).toNat = i.toNat) :
    (buckets.update i d h).WF := by
  refine ⟨fun l hl => ?_, fun i hi p hp => ?_, ?_⟩
  · rw [update_get]
    split
    · exact h₁ (H.1 _ _)
    · exact H.1 _ (by simpa using hl)
  · revert hp; simp [update_data, Array.getElem_eq_data_get, List.get_set]
    split <;> intro hp
    · next eq => exact eq ▸ h₂ (H.2 _ _) _ hp
    · simp at hi; exact H.2 i hi _ hp
  · simpa using H.3

end Buckets

@[simp] theorem reinsertAux_size' [Hashable α] (data : Buckets α β) (a : α) (b : β) :
    (reinsertAux data a b).1.size = data.1.size := by
  dsimp only [reinsertAux]
  split <;> simp

theorem reinsertAux_size [Hashable α] (data : Buckets α β) (hd : 0 < data.1.size) (a : α) (b : β) :
    (reinsertAux data a b).size = data.size + 1 := by
  simp [Buckets.size_eq, reinsertAux, hd]
  refine have ⟨l₁, l₂, h₁, _, eq⟩ := Buckets.exists_of_update ..; eq ▸ ?_
  simp [h₁, Nat.succ_add]; rfl

theorem reinsertAux_WF [BEq α] [Hashable α] {data : Buckets α β} {a : α} {b : β} (H : data.WF)
    (h₁ : ∀ [PartialEquivBEq α] [LawfulHashable α],
      haveI := mkIdx H.3 (hash a).toUSize
      data.1[this.1].contains a = false)
      --data.1[this.1].All fun x _ => ¬(a == x))--
       :
    (reinsertAux data a b).WF := by
  simp only [reinsertAux, Array.data_length, H.3, ↓reduceDite, Array.ugetElem_eq_getElem]
  apply H.update
  · intros
    apply AssocList.WF.cons
    apply h₁
  · simp

theorem expand_size'.foldl [Hashable α] (l : AssocList α β) (target : Buckets α β) :
    (l.foldl reinsertAux target).1.size = target.1.size := by
  induction l generalizing target <;> simp_all

instance : Associative (α := Nat) (.+.) := ⟨Nat.add_assoc⟩
instance : Commutative (α := Nat) (.+.) := ⟨Nat.add_comm⟩

theorem expand_size.foldl [Hashable α] {l : AssocList α β} (target : Buckets α β)
    (ht : 0 < target.1.size) :
    (l.foldl reinsertAux target).size = target.size + l.toList.length := by
  induction l generalizing target
  · simp
  · next k v t ih =>
    simp only [AssocList.foldl_eq, AssocList.toList, List.foldl_cons, List.length_cons,
      Nat.succ_eq_add_one]
    specialize ih (reinsertAux target k v)
    simp only [Array.data_length, reinsertAux_size', AssocList.foldl_eq] at ih
    rw [ih ht, reinsertAux_size _ ht]
    ac_rfl

theorem expand.go_of_lt [Hashable α] {i : Nat} {source : Array (AssocList α β)}
    {target : Buckets α β} (h : i < source.size) :
    expand.go i source target = expand.go (i + 1) (source.set ⟨i, h⟩ .nil)
      ((source.get ⟨i, h⟩).foldl reinsertAux target) := by
  rw [expand.go]
  simp only [h, dite_true]

theorem expand.go_of_not_lt [Hashable α] {i : Nat} {source : Array (AssocList α β)}
    {target : Buckets α β} (h : ¬i < source.size) :
    expand.go i source target = target := by
  rw [expand.go]
  simp only [h, dite_false]


theorem expand_size [Hashable α] {buckets : Buckets α β} (hd : 0 < buckets.1.size) :
    (expand sz buckets).buckets.size = buckets.size := by
  rw [expand, go]
  · rw [Buckets.mk_size, Buckets.size, Nat.add_zero, List.drop_zero]
  · rwa [Buckets.mk_size', Nat.mul_pos_iff_of_pos_right Nat.two_pos]
  where
    go (i source) (target : Buckets α β) (ht : 0 < target.1.size) :
        (expand.go i source target).size =
          .sum ((source.data.drop i).map (·.toList.length)) + target.size := by
      induction i, source, target using expand.go.induct
      · next i source target hi _ es newSource newTarget ih =>
        simp only [newSource, newTarget, es] at *
        rw [expand.go_of_lt hi]
        refine (ih ?_).trans ?_
        · simpa only [expand_size'.foldl]
        · rw [Array.size_eq_length_data] at hi
          rw [List.drop_eq_get_cons hi, List.map_cons, Nat.sum_cons, Array.data_set,
            List.drop_set_of_lt _ _ (Nat.lt_succ_self i), expand_size.foldl _ ht,
            Array.get_eq_getElem, Array.getElem_eq_data_get]
          ac_rfl
      · next i source target hi =>
        rw [expand.go_of_not_lt hi]
        rw [Array.size_eq_length_data, Nat.not_lt, ← List.drop_eq_nil_iff_le] at hi
        simp [hi]

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
    simp [reinsertAux, Buckets.update, ht₁.3] at h
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
  go _ H.1 H.2 ⟨.mk' (Nat.mul_pos H.3 (by decide)),
    fun _ _ _ _ => by simp_all [Buckets.mk, List.mem_replicate]⟩
where
  go (i) {source : Array (AssocList α β)}
      (hs₁ : ∀ [LawfulHashable α] [PartialEquivBEq α], ∀ (j : Nat) (h : j < source.size),
        source[j].toList.Pairwise fun a b => ¬(a.1 == b.1))
      (hs₂ : ∀ (j : Nat) (h : j < source.size),
        source[j].All fun k _ => ((hash k).toUSize % source.size).toNat = j)
      {target : Buckets α β} (ht : target.WF ∧ ∀ bucket ∈ target.1.data,
        bucket.All fun k _ => ((hash k).toUSize % source.size).toNat < i) :
      (expand.go i source target).WF := by
    unfold expand.go; split
    · next H =>
      refine go (i+1) (fun _ hl => ?_) (fun i h => ?_) ?_
      · rw [Array.get_set _ _ _ (by simpa using hl)]
        split
        · simp
        · apply hs₁
      · simp [Array.getElem_eq_data_get, List.get_set]; split
        · nofun
        · exact hs₂ _ (by simp_all)
      · let rank (k : α) := ((hash k).toUSize % source.size).toNat
        have := expand_WF.foldl rank ?_ (hs₂ _ H) ht.1 (fun _ h₁ _ h₂ => ?_)
        · simp only [Array.get_eq_getElem, AssocList.foldl_eq, Array.size_set]
          exact ⟨this.1, fun _ h₁ _ h₂ => Nat.lt_succ_of_le (this.2 _ h₁ _ h₂)⟩
        · exact hs₁ _ _
        · have := ht.2 _ h₁ _ h₂
          refine ⟨Nat.le_of_lt this, fun _ h h' => Nat.ne_of_lt this ?_⟩
          exact LawfulHashable.hash_eq h' ▸ hs₂ _ H _ h
    · exact ht.1
  termination_by source.size - i

theorem insert_size [BEq α] [Hashable α] {m : Imp α β} (hm : 0 < m.2.1.size) {k v}
    (h : m.size = m.buckets.size) :
    (insert m k v).size = (insert m k v).buckets.size := by
  simp only [insert, hm]
  dsimp [cond]; split
  · unfold Buckets.size
    refine have ⟨_, _, h₁, _, eq⟩ := Buckets.exists_of_update ..; eq ▸ ?_
    simp [h, h₁, Buckets.size_eq]
  split
  · unfold Buckets.size
    refine have ⟨_, _, h₁, _, eq⟩ := Buckets.exists_of_update ..; eq ▸ ?_
    simp [h, h₁, Buckets.size_eq, Nat.succ_add]; rfl
  · rw [expand_size (by simpa)]; simp [h, expand, Buckets.size]
    refine have ⟨_, _, h₁, _, eq⟩ := Buckets.exists_of_update ..; eq ▸ ?_
    simp [h₁, Buckets.size_eq, Nat.succ_add]; rfl

private theorem mem_replaceF {l : List (α × β)} {x : α × β} {p : α × β → Bool} {f : α × β → β} :
    x ∈ (l.replaceF fun a => bif p a then some (k, f a) else none) → x.1 = k ∨ x ∈ l := by
  induction l with
  | nil => exact .inr
  | cons a l ih =>
    simp; generalize e : cond .. = z; revert e
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
    simp at H ⊢
    generalize e : cond .. = z; unfold cond at e; revert e
    split <;> (intro h; subst h; simp)
    · next e => exact ⟨(H.1 · · ∘ PartialEquivBEq.trans e), H.2⟩
    · next e =>
      refine ⟨fun a h => ?_, ih H.2⟩
      match mem_replaceF h with
      | .inl eq => exact eq ▸ ne_true_of_eq_false e
      | .inr h => exact H.1 a h

theorem insert_WF [BEq α] [Hashable α] {m : Imp α β} {k v}
    (h : m.buckets.WF) : (insert m k v).buckets.WF := by
  simp only [insert, h.3]
  dsimp [cond]; split
  · next h₁ =>
    simp at h₁; have ⟨x, hx₁, hx₂⟩ := h₁
    refine h.update (fun H => ?_) (fun H a h => ?_)
    · simp; exact pairwise_replaceF H
    · simp [AssocList.All] at H h ⊢
      match mem_replaceF h with
      | .inl rfl => rfl
      | .inr h => exact H _ h
  · next h₁ =>
    rw [Bool.eq_false_iff] at h₁; simp at h₁
    suffices _ by split <;> [exact this; refine expand_WF this]
    refine h.update (.cons ?_) (fun H a h => ?_)
    · exact fun a h h' => h₁ a h (PartialEquivBEq.symm h')
    · cases h with
      | head => rfl
      | tail _ h => exact H _ h

theorem erase_size [BEq α] [Hashable α] {m : Imp α β} (hm : 0 < m.2.1.size) {k}
    (h : m.size = m.buckets.size) :
    (erase m k).size = (erase m k).buckets.size := by
  simp only [erase, hm]
  dsimp [cond]; split
  · next H =>
    simp [h, Buckets.size]
    refine have ⟨_, _, h₁, _, eq⟩ := Buckets.exists_of_update ..; eq ▸ ?_
    simp [h, h₁, Buckets.size_eq]
    rw [(_ : List.length _ = _ + 1), Nat.add_right_comm]; {rfl}
    clear h₁ eq
    simp [AssocList.contains_eq] at H
    have ⟨a, h₁, h₂⟩ := H
    refine have ⟨_, _, _, _, _, h, eq⟩ := List.exists_of_eraseP h₁ h₂; eq ▸ ?_
    simp [h]; rfl
  · exact h

theorem erase_WF [BEq α] [Hashable α] {m : Imp α β} {k}
    (h : m.buckets.WF) : (erase m k).buckets.WF := by
  simp only [erase, h.3]
  dsimp [cond]; split
  · refine h.update (fun H => ?_) (fun H a h => ?_) <;> simp at h ⊢
    · exact H.sublist (List.eraseP_sublist _)
    · exact H _ (List.mem_of_mem_eraseP h)
  · exact h

theorem modify_size [BEq α] [Hashable α] {m : Imp α β} (hm : 0 < m.2.1.size) {k}
    (h : m.size = m.buckets.size) :
    (modify m k f).size = (modify m k f).buckets.size := by
  simp only [modify, hm]
  dsimp [cond]; rw [Buckets.update_update]
  simp [h, Buckets.size]
  refine have ⟨_, _, h₁, _, eq⟩ := Buckets.exists_of_update ..; eq ▸ ?_
  simp [h, h₁, Buckets.size_eq]

theorem modify_WF [BEq α] [Hashable α] {m : Imp α β} {k}
    (h : m.buckets.WF) : (modify m k f).buckets.WF := by
  simp only [modify, h.3]
  dsimp [cond]; rw [Buckets.update_update]
  refine h.update (fun H => ?_) (fun H a h => ?_) <;> simp at h ⊢
  · exact pairwise_replaceF H
  · simp [AssocList.All] at H h ⊢
    match mem_replaceF h with
    | .inl rfl => rfl
    | .inr h => exact H _ h

theorem WF.out [BEq α] [Hashable α] {m : Imp α β} (h : m.WF) :
    m.size = m.buckets.size ∧ m.buckets.WF := by
  induction h with
  | mk h₁ h₂ => exact ⟨h₁, h₂⟩
  | @empty' _ h => exact ⟨(Buckets.mk_size).symm, .mk' h⟩
  | insert _ ih => exact ⟨insert_size ih.2.3 ih.1, insert_WF ih.2⟩
  | erase _ ih => exact ⟨erase_size ih.2.3 ih.1, erase_WF ih.2⟩
  | modify _ ih => exact ⟨modify_size ih.2.3 ih.1, modify_WF ih.2⟩

theorem WF_iff [BEq α] [Hashable α] {m : Imp α β} :
    m.WF ↔ m.size = m.buckets.size ∧ m.buckets.WF :=
  ⟨(·.out), fun ⟨h₁, h₂⟩ => .mk h₁ h₂⟩

theorem WF.mapVal {α β γ} {f : α → β → γ} [BEq α] [Hashable α]
    {m : Imp α β} (H : WF m) : WF (mapVal f m) := by
  have ⟨h₁, h₂⟩ := H.out
  simp [Imp.mapVal, Buckets.mapVal, WF_iff, h₁]; refine ⟨?_, ?_, fun i h => ?_, ?_⟩
  · simp [Buckets.size]; congr; funext l; simp
  · simp only [Array.size_map, Array.getElem_map, AssocList.toList_mapVal, List.pairwise_map]
    exact fun _ => h₂.1 _
  · simp [AssocList.All] at h ⊢
    intro a m
    apply h₂.2 _ _ _ m
  · simpa using H.out.2.3

theorem WF.filterMap {α β γ} {f : α → β → Option γ} [BEq α] [Hashable α]
    {m : Imp α β} (H : WF m) : WF (filterMap f m) := by
  let g₁ (l : AssocList α β) := l.toList.filterMap (fun x => (f x.1 x.2).map (x.1, ·))
  have H1 (l n acc) : filterMap.go f acc l n =
      (((g₁ l).reverse ++ acc.toList).toAssocList, ⟨n.1 + (g₁ l).length⟩) := by
    induction l generalizing n acc with simp [filterMap.go, g₁, *]
    | cons a b l => match f a b with
      | none => rfl
      | some c => simp; rw [Nat.add_right_comm]; rfl
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
      simp; exact match f a.1 a.2 with
      | none => .cons _ ih
      | some b => .cons₂ _ ih
  suffices ∀ (bk : Array (AssocList α γ)) sz,
    m.buckets.1.mapM (m := M) (filterMap.go f .nil) ⟨0⟩ = (bk, ⟨sz⟩) →
    WF ⟨sz, ⟨bk⟩⟩ from this _ _ rfl
  simp [Array.mapM_eq_mapM_data, bind, StateT.bind, H2, g]
  intro bk sz e'; cases e'
  refine .mk (by simp [Buckets.size]) ⟨?_, fun i h => ?_, ?_⟩
  · simp only [Array.size_mk, List.length_map, Array.data_length]
    sorry -- this will all follow once we know more about everything
    -- refine fun l h => (List.pairwise_reverse.2 ?_).imp (mt PartialEquivBEq.symm)
    -- have := H.out.2.1 _ h
    -- rw [← List.pairwise_map (R := (¬ · == ·))] at this ⊢
    -- exact this.sublist (H3 l.toList)
  · simp only [Array.size_mk, List.length_map, Array.data_length, Array.getElem_eq_data_get,
      List.get_map] at h ⊢
    have := H.out.2.2 _ h
    simp [AssocList.All, g₁] at this ⊢
    rintro _ _ h' _ _ rfl
    exact this _ h'
  · simpa using H.out.2.3

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

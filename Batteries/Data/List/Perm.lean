/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad, Mario Carneiro
-/
module

public import Batteries.Tactic.Alias
public import Batteries.Data.List.Count
import Batteries.Util.ProofWanted

@[expose] public section

/-!
# List Permutations

This file introduces the `List.Perm` relation, which is true if two lists are permutations of one
another.

## Notation

The notation `~` is used for permutation equivalence.
-/

open Nat

namespace List

open Perm (swap)

@[simp] theorem nil_subperm {l : List α} : [] <+~ l := ⟨[], Perm.nil, by simp⟩

theorem Perm.subperm_left {l l₁ l₂ : List α} (p : l₁ ~ l₂) : l <+~ l₁ ↔ l <+~ l₂ :=
  suffices ∀ {l₁ l₂ : List α}, l₁ ~ l₂ → l <+~ l₁ → l <+~ l₂ from ⟨this p, this p.symm⟩
  fun p ⟨_u, pu, su⟩ =>
  let ⟨v, pv, sv⟩ := exists_perm_sublist su p
  ⟨v, pv.trans pu, sv⟩

theorem Perm.subperm_right {l₁ l₂ l : List α} (p : l₁ ~ l₂) : l₁ <+~ l ↔ l₂ <+~ l :=
  ⟨fun ⟨u, pu, su⟩ => ⟨u, pu.trans p, su⟩, fun ⟨u, pu, su⟩ => ⟨u, pu.trans p.symm, su⟩⟩

theorem Sublist.subperm {l₁ l₂ : List α} (s : l₁ <+ l₂) : l₁ <+~ l₂ := ⟨l₁, .rfl, s⟩

theorem Perm.subperm {l₁ l₂ : List α} (p : l₁ ~ l₂) : l₁ <+~ l₂ := ⟨l₂, p.symm, Sublist.refl _⟩

@[refl] theorem Subperm.refl (l : List α) : l <+~ l := Perm.rfl.subperm

theorem Subperm.trans {l₁ l₂ l₃ : List α} (s₁₂ : l₁ <+~ l₂) (s₂₃ : l₂ <+~ l₃) : l₁ <+~ l₃ :=
  let ⟨_l₂', p₂, s₂⟩ := s₂₃
  let ⟨l₁', p₁, s₁⟩ := p₂.subperm_left.2 s₁₂
  ⟨l₁', p₁, s₁.trans s₂⟩

theorem Subperm.cons_self : l <+~ a :: l := ⟨l, .refl _, sublist_cons_self ..⟩

theorem Subperm.cons_right {α : Type _} {l l' : List α} (x : α) (h : l <+~ l') : l <+~ x :: l' :=
  h.trans (sublist_cons_self x l').subperm

theorem Subperm.length_le {l₁ l₂ : List α} : l₁ <+~ l₂ → length l₁ ≤ length l₂
  | ⟨_l, p, s⟩ => p.length_eq ▸ s.length_le

theorem Subperm.perm_of_length_le {l₁ l₂ : List α} : l₁ <+~ l₂ → length l₂ ≤ length l₁ → l₁ ~ l₂
  | ⟨_l, p, s⟩, h => (s.eq_of_length_le <| p.symm.length_eq ▸ h) ▸ p.symm

theorem Subperm.antisymm {l₁ l₂ : List α} (h₁ : l₁ <+~ l₂) (h₂ : l₂ <+~ l₁) : l₁ ~ l₂ :=
  h₁.perm_of_length_le h₂.length_le

theorem Subperm.subset {l₁ l₂ : List α} : l₁ <+~ l₂ → l₁ ⊆ l₂
  | ⟨_l, p, s⟩ => Subset.trans p.symm.subset s.subset

theorem Subperm.filter (p : α → Bool) ⦃l l' : List α⦄ (h : l <+~ l') :
    filter p l <+~ filter p l' := by
  let ⟨xs, hp, h⟩ := h
  exact ⟨_, hp.filter p, h.filter p⟩

@[simp] theorem subperm_nil : l <+~ [] ↔ l = [] :=
  ⟨fun h => length_eq_zero_iff.1 $ Nat.le_zero.1 h.length_le, by rintro rfl; rfl⟩

@[simp] theorem singleton_subperm_iff {α} {l : List α} {a : α} : [a] <+~ l ↔ a ∈ l := by
  refine ⟨fun ⟨s, hla, h⟩ => ?_, fun h => ⟨[a], .rfl, singleton_sublist.mpr h⟩⟩
  rwa [perm_singleton.mp hla, singleton_sublist] at h

theorem Subperm.countP_le (p : α → Bool) {l₁ l₂ : List α} : l₁ <+~ l₂ → countP p l₁ ≤ countP p l₂
  | ⟨_l, p', s⟩ => p'.countP_eq p ▸ s.countP_le

theorem Subperm.count_le [BEq α] {l₁ l₂ : List α} (s : l₁ <+~ l₂) (a) :
    count a l₁ ≤ count a l₂ := s.countP_le _

theorem subperm_cons (a : α) {l₁ l₂ : List α} : a :: l₁ <+~ a :: l₂ ↔ l₁ <+~ l₂ := by
  refine ⟨fun ⟨l, p, s⟩ => ?_, fun ⟨l, p, s⟩ => ⟨a :: l, p.cons a, s.cons₂ _⟩⟩
  match s with
  | .cons _ s' => exact (p.subperm_left.2 <| (sublist_cons_self _ _).subperm).trans s'.subperm
  | .cons₂ _ s' => exact ⟨_, p.cons_inv, s'⟩

/-- Weaker version of `Subperm.cons_left` -/
theorem cons_subperm_of_not_mem_of_mem {a : α} {l₁ l₂ : List α} (h₁ : a ∉ l₁) (h₂ : a ∈ l₂)
    (s : l₁ <+~ l₂) : a :: l₁ <+~ l₂ := by
  obtain ⟨l, p, s⟩ := s
  induction s generalizing l₁ with
  | slnil => cases h₂
  | @cons r₁ _ b s' ih =>
    simp at h₂
    match h₂ with
    | .inl e => subst_vars; exact ⟨_ :: r₁, p.cons _, s'.cons₂ _⟩
    | .inr m => let ⟨t, p', s'⟩ := ih h₁ m p; exact ⟨t, p', s'.cons _⟩
  | @cons₂ _ r₂ b _ ih =>
    have bm : b ∈ l₁ := p.subset mem_cons_self
    have am : a ∈ r₂ := by
      simp only [mem_cons] at h₂
      exact h₂.resolve_left fun e => h₁ <| e.symm ▸ bm
    obtain ⟨t₁, t₂, rfl⟩ := append_of_mem bm
    have st : t₁ ++ t₂ <+ t₁ ++ b :: t₂ := by simp
    obtain ⟨t, p', s'⟩ := ih (mt (st.subset ·) h₁) am (.cons_inv <| p.trans perm_middle)
    exact ⟨b :: t, (p'.cons b).trans <| (swap ..).trans (perm_middle.symm.cons a), s'.cons₂ _⟩

theorem subperm_append_left {l₁ l₂ : List α} : ∀ l, l ++ l₁ <+~ l ++ l₂ ↔ l₁ <+~ l₂
  | [] => .rfl
  | a :: l => (subperm_cons a).trans (subperm_append_left l)

theorem subperm_append_right {l₁ l₂ : List α} (l) : l₁ ++ l <+~ l₂ ++ l ↔ l₁ <+~ l₂ :=
  (perm_append_comm.subperm_left.trans perm_append_comm.subperm_right).trans (subperm_append_left l)

theorem Subperm.exists_of_length_lt {l₁ l₂ : List α} (s : l₁ <+~ l₂) (h : length l₁ < length l₂) :
    ∃ a, a :: l₁ <+~ l₂ := by
  obtain ⟨l, p, s⟩ := s
  suffices length l < length l₂ → ∃ a : α, a :: l <+~ l₂ from
    (this <| p.symm.length_eq ▸ h).imp fun a => (p.cons a).subperm_right.1
  clear h p l₁
  induction s with intro h
  | slnil => cases h
  | cons a s IH =>
    match Nat.lt_or_eq_of_le (Nat.le_of_lt_succ h) with
    | .inl h => exact (IH h).imp fun a s => s.trans (sublist_cons_self _ _).subperm
    | .inr h => exact ⟨a, s.eq_of_length h ▸ .refl _⟩
  | cons₂ b _ IH =>
    exact (IH <| Nat.lt_of_succ_lt_succ h).imp fun a s =>
      (swap ..).subperm_right.1 <| (subperm_cons _).2 s

theorem subperm_of_subset (d : Nodup l₁) (H : l₁ ⊆ l₂) : l₁ <+~ l₂ := by
  induction d with
  | nil => exact ⟨nil, .nil, nil_sublist _⟩
  | cons h _ IH =>
    have ⟨H₁, H₂⟩ := forall_mem_cons.1 H
    exact cons_subperm_of_not_mem_of_mem (h _ · rfl) H₁ (IH H₂)

theorem perm_ext_iff_of_nodup {l₁ l₂ : List α} (d₁ : Nodup l₁) (d₂ : Nodup l₂) :
    l₁ ~ l₂ ↔ ∀ a, a ∈ l₁ ↔ a ∈ l₂ := by
  refine ⟨fun p _ => p.mem_iff, fun H => ?_⟩
  exact (subperm_of_subset d₁ fun a => (H a).1).antisymm <| subperm_of_subset d₂ fun a => (H a).2

theorem Nodup.perm_iff_eq_of_sublist {l₁ l₂ l : List α} (d : Nodup l)
    (s₁ : l₁ <+ l) (s₂ : l₂ <+ l) : l₁ ~ l₂ ↔ l₁ = l₂ := by
  refine ⟨fun h => ?_, fun h => by rw [h]⟩
  induction s₂ generalizing l₁ with simp [Nodup, List.forall_mem_ne] at d
  | slnil => exact h.eq_nil
  | cons a s₂ IH =>
    match s₁ with
    | .cons _ s₁ => exact IH d.2 s₁ h
    | .cons₂ _ s₁ =>
      have := Subperm.subset ⟨_, h.symm, s₂⟩ (.head _)
      exact (d.1 this).elim
  | cons₂ a _ IH =>
    match s₁ with
    | .cons _ s₁ =>
      have := Subperm.subset ⟨_, h, s₁⟩ (.head _)
      exact (d.1 this).elim
    | .cons₂ _ s₁ => rw [IH d.2 s₁ h.cons_inv]

theorem subperm_cons_erase [BEq α] [LawfulBEq α] (a : α) (l : List α) : l <+~ a :: l.erase a :=
  if h : a ∈ l then
    (perm_cons_erase h).subperm
  else
    (erase_of_not_mem h).symm ▸ (sublist_cons_self _ _).subperm

theorem erase_subperm [BEq α] (a : α) (l : List α) : l.erase a <+~ l := erase_sublist.subperm

theorem Subperm.erase [BEq α] [LawfulBEq α] (a : α) (h : l₁ <+~ l₂) : l₁.erase a <+~ l₂.erase a :=
  let ⟨l, hp, hs⟩ := h
  ⟨l.erase a, hp.erase _, hs.erase _⟩

theorem Perm.diff_right [BEq α] [LawfulBEq α] (t : List α) (h : l₁ ~ l₂) :
    l₁.diff t ~ l₂.diff t := by
  induction t generalizing l₁ l₂ h with simp only [List.diff]
  | nil => exact h
  | cons x t ih =>
    simp only [elem_eq_mem, decide_eq_true_eq, Perm.mem_iff h]
    split
    · exact ih (h.erase _)
    · exact ih h

theorem Perm.diff_left [BEq α] [LawfulBEq α] (l : List α) (h : t₁ ~ t₂) :
    l.diff t₁ = l.diff t₂ := by
  induction h generalizing l with try simp [List.diff]
  | cons x _ ih => apply ite_congr rfl <;> (intro; apply ih)
  | swap x y =>
    have : DecidableEq α := instDecidableEqOfLawfulBEq
    if h : x = y then
      simp [h]
    else
      simp [mem_erase_of_ne h, mem_erase_of_ne (Ne.symm h), erase_comm x y]
      split <;> simp
  | trans => simp only [*]

theorem Perm.diff [BEq α] [LawfulBEq α] {l₁ l₂ t₁ t₂ : List α} (hl : l₁ ~ l₂) (ht : t₁ ~ t₂) :
    l₁.diff t₁ ~ l₂.diff t₂ :=
  ht.diff_left l₂ ▸ hl.diff_right _

theorem Subperm.diff_right [BEq α] [LawfulBEq α] (h : l₁ <+~ l₂) (t : List α) :
    l₁.diff t <+~ l₂.diff t := by
  induction t generalizing l₁ l₂ h with simp [List.diff, *]
  | cons x t ih =>
    split <;> rename_i hx1
    · simp [h.subset hx1]
      exact ih (h.erase _)
    · split
      · rw [← erase_of_not_mem hx1]
        exact ih (h.erase _)
      · exact ih h

theorem erase_cons_subperm_cons_erase [BEq α] [LawfulBEq α] (a b : α) (l : List α) :
    (a :: l).erase b <+~ a :: l.erase b := by
  if h : a = b then
    rw [h, erase_cons_head]; apply subperm_cons_erase
  else
    have : ¬(a == b) = true := by simp only [beq_false_of_ne h, not_false_eq_true, reduceCtorEq]
    rw [erase_cons_tail this]

theorem subperm_cons_diff [BEq α] [LawfulBEq α] {a : α} {l₁ l₂ : List α} :
    (a :: l₁).diff l₂ <+~ a :: l₁.diff l₂ := by
  induction l₂ with
  | nil => exact ⟨a :: l₁, by simp [List.diff]⟩
  | cons b l₂ ih =>
    rw [diff_cons, diff_cons, ← diff_erase, ← diff_erase]
    exact Subperm.trans (.erase _ ih) (erase_cons_subperm_cons_erase ..)

theorem subset_cons_diff [BEq α] [LawfulBEq α] {a : α} {l₁ l₂ : List α} :
    (a :: l₁).diff l₂ ⊆ a :: l₁.diff l₂ :=
  subperm_cons_diff.subset

/-- The list version of `add_tsub_cancel_of_le` for multisets. -/
theorem subperm_append_diff_self_of_count_le [BEq α] [LawfulBEq α] {l₁ l₂ : List α}
    (h : ∀ x ∈ l₁, count x l₁ ≤ count x l₂) : l₁ ++ l₂.diff l₁ ~ l₂ := by
  induction l₁ generalizing l₂ with
  | nil => simp
  | cons hd tl IH =>
    have : hd ∈ l₂ := by
      rw [← count_pos_iff]
      exact Nat.lt_of_lt_of_le (count_pos_iff.mpr (.head _)) (h hd (.head _))
    have := perm_cons_erase this
    refine Perm.trans ?_ this.symm
    rw [cons_append, diff_cons, perm_cons]
    refine IH fun x hx => ?_
    specialize h x (.tail _ hx)
    rw [perm_iff_count.mp this] at h
    if hx : hd = x then subst hd; simpa [Nat.succ_le_succ_iff] using h
    else simpa [hx] using h

/-- The list version of `Multiset.le_iff_count`. -/
theorem subperm_ext_iff [BEq α] [LawfulBEq α] {l₁ l₂ : List α} :
    l₁ <+~ l₂ ↔ ∀ x ∈ l₁, count x l₁ ≤ count x l₂ := by
  refine ⟨fun h x _ => h.count_le x, fun h => ?_⟩
  have : l₁ <+~ l₂.diff l₁ ++ l₁ := (subperm_append_right l₁).mpr nil_subperm
  refine this.trans (Perm.subperm ?_)
  exact perm_append_comm.trans (subperm_append_diff_self_of_count_le h)

theorem isSubperm_iff [BEq α] [LawfulBEq α] {l₁ l₂ : List α} : l₁.isSubperm l₂ ↔ l₁ <+~ l₂ := by
  simp [isSubperm, subperm_ext_iff]

instance decidableSubperm [BEq α] [LawfulBEq α] :
    DecidableRel ((· <+~ ·) : List α → List α → Prop) := fun _ _ =>
  decidable_of_iff _ isSubperm_iff

theorem Subperm.cons_left [BEq α] [LawfulBEq α] (h : l₁ <+~ l₂) (x : α)
    (hx : count x l₁ < count x l₂) : x :: l₁ <+~ l₂ := by
  rw [subperm_ext_iff] at h ⊢
  intro y hy
  if hy' : y = x then
    subst x; simpa using Nat.succ_le_of_lt hx
  else
    rw [count_cons_of_ne (Ne.symm hy')]
    refine h y ?_
    simpa [hy'] using hy

theorem Perm.union_right [BEq α] [LawfulBEq α] (t₁ : List α) (h : l₁ ~ l₂) :
    l₁ ∪ t₁ ~ l₂ ∪ t₁ := by
  induction h with
  | nil => rfl
  | cons a _ ih => exact ih.insert a
  | swap => apply perm_insert_swap
  | trans _ _ ih_1 ih_2 => exact ih_1.trans ih_2

theorem Perm.union_left [BEq α] [LawfulBEq α] (l : List α) (h : t₁ ~ t₂) : l ∪ t₁ ~ l ∪ t₂ := by
  induction l with
  | nil => simp only [nil_union, h]
  | cons _ _ ih => simp only [cons_union, Perm.insert _ ih]

theorem Perm.union [BEq α] [LawfulBEq α] {l₁ l₂ t₁ t₂ : List α} (p₁ : l₁ ~ l₂) (p₂ : t₁ ~ t₂) :
    l₁ ∪ t₁ ~ l₂ ∪ t₂ :=
  (p₁.union_right t₁).trans (p₂.union_left l₂)

theorem Perm.inter_right [BEq α] (t₁ : List α) : l₁ ~ l₂ → l₁ ∩ t₁ ~ l₂ ∩ t₁ := .filter _

theorem Perm.inter_left [BEq α] [LawfulBEq α] (l : List α) (p : t₁ ~ t₂) : l ∩ t₁ = l ∩ t₂ :=
  filter_congr fun a _ => by simpa using p.mem_iff (a := a)

theorem Perm.inter [BEq α] [LawfulBEq α] {l₁ l₂ t₁ t₂ : List α} (p₁ : l₁ ~ l₂) (p₂ : t₁ ~ t₂) :
    l₁ ∩ t₁ ~ l₂ ∩ t₂ :=
  p₂.inter_left l₂ ▸ p₁.inter_right t₁

theorem Perm.flatten_congr :
    ∀ {l₁ l₂ : List (List α)} (_ : List.Forall₂ (· ~ ·) l₁ l₂), l₁.flatten ~ l₂.flatten
  | _, _, .nil => .rfl
  | _ :: _, _ :: _, .cons h₁ h₂ => h₁.append (Perm.flatten_congr h₂)

theorem perm_insertP (p : α → Bool) (a l) : insertP p a l ~ a :: l := by
  induction l with simp [insertP, insertP.loop, cond]
  | cons _ _ ih =>
    split
    · exact Perm.refl ..
    · rw [insertP_loop, reverseAux, reverseAux]
      exact Perm.trans (Perm.cons _ ih) (Perm.swap ..)

theorem Perm.insertP (p : α → Bool) (a) (h : l₁ ~ l₂) : insertP p a l₁ ~ insertP p a l₂ :=
  Perm.trans (perm_insertP ..) <| Perm.trans (Perm.cons _ h) <| Perm.symm (perm_insertP ..)

/-! ### idxInj  -/

/-- `Subperm.idxInj` is an injective map from `Fin xs.length` to `Fin ys.length`
which exists when we have `xs <+~ ys`: conceptually it represents an embedding of
one list into the other. For example:
```
(by decide : [1, 0, 1] <+~ [5, 0, 1, 3, 1]).idxInj 1 = 1
```
-/
def Subperm.idxInj [BEq α] [ReflBEq α] {xs ys : List α} (h : xs <+~ ys) (i : Fin xs.length) :
    Fin ys.length :=
  ⟨ys.idxOfNth xs[i.1] (xs.countBefore xs[i] i), idxOfNth_lt_length_of_lt_count <|
    Nat.lt_of_lt_of_le countBefore_lt_count_getElem <| h.count_le _⟩

@[simp, grind =]
theorem coe_idxInj [BEq α] [ReflBEq α] {xs ys : List α} {h : xs <+~ ys}
    {i : Fin xs.length} :
    (h.idxInj i : Nat) = ys.idxOfNth xs[i] (xs.countBefore xs[i] i) := rfl

theorem Subperm.getElem_idxInj_eq_getElem [BEq α] [LawfulBEq α] {xs ys : List α}
    (h : xs <+~ ys) {i : Fin xs.length} :
  ys[(h.idxInj i : Nat)] = xs[(i : Nat)] := getElem_idxOfNth_eq

theorem Subperm.idxInj_injective [BEq α] [LawfulBEq α] {xs ys : List α}
    (h : xs <+~ ys) : h.idxInj.Injective := fun _ _ hij => by
  have H := congrArg (fun i : Fin ys.length => xs.idxOfNth ys[i] (ys.countBefore ys[i] i)) hij
  grind

@[simp]
theorem Subperm.idxInj_inj [BEq α] [LawfulBEq α] {xs ys : List α}
    {h : xs <+~ ys} (i j : Fin xs.length) :
  h.idxInj i = h.idxInj j ↔ i = j := h.idxInj_injective.eq_iff

/-! ### idxBij -/

/-- `Perm.idxBij` is a bijective map from `Fin xs.length` to `Fin ys.length`
which exists when we have `xs.Perm ys`: conceptually it represents a permuting of
one list into the other. For example:
```
(by decide : [0, 1, 1, 3, 5] ~ [5, 0, 1, 3, 1]).idxBij 2 = 4
```
-/
def Perm.idxBij [BEq α] [ReflBEq α] {xs ys : List α} (h : xs ~ ys) :
    Fin xs.length → Fin ys.length := h.subperm.idxInj

@[simp, grind =]
theorem Perm.subperm_idxBij [BEq α] [ReflBEq α] {xs ys : List α} (h : xs ~ ys) :
    h.subperm.idxInj = h.idxBij := rfl

@[simp, grind =]
theorem Perm.coe_idxBij [BEq α] [ReflBEq α] {xs ys : List α} (h : xs ~ ys)
    {i : Fin xs.length} : (h.idxBij i : Nat) = ys.idxOfNth xs[i] (xs.countBefore xs[i] i) := rfl

theorem Perm.getElem_idxBij_eq_getElem [BEq α] [LawfulBEq α] {xs ys : List α}
    (hxy : xs.Perm ys) (i : Fin xs.length) : ys[(hxy.idxBij i : Nat)] = xs[(i : Nat)] :=
  getElem_idxOfNth_eq

theorem Perm.getElem_idxBij_symm_eq_getElem [BEq α] [LawfulBEq α] {xs ys : List α}
    (hxy : xs.Perm ys) (i : Fin ys.length) : xs[(hxy.symm.idxBij i : Nat)] = ys[(i : Nat)] :=
  getElem_idxOfNth_eq

theorem Perm.idxBij_leftInverse_idxBij_symm [BEq α] [LawfulBEq α] {xs ys : List α} (h : xs ~ ys) :
    h.idxBij.LeftInverse h.symm.idxBij := by grind

theorem Perm.idxBij_rightInverse_idxBij_symm [BEq α] [LawfulBEq α] {xs ys : List α} (h : xs ~ ys) :
    h.idxBij.RightInverse h.symm.idxBij := by grind

theorem Perm.idxBij_symm_rightInverse_idxBij [BEq α] [LawfulBEq α] {xs ys : List α} (h : xs ~ ys) :
    h.symm.idxBij.RightInverse h.idxBij := h.idxBij_leftInverse_idxBij_symm

theorem Perm.idxBij_symm_leftInverse_idxBij [BEq α] [LawfulBEq α] {xs ys : List α} (h : xs ~ ys) :
    h.symm.idxBij.LeftInverse h.idxBij := h.idxBij_rightInverse_idxBij_symm

theorem Perm.idxBij_idxBij_symm [BEq α] [LawfulBEq α] {xs ys : List α} (h : xs ~ ys)
    {i : Fin ys.length} : h.idxBij (h.symm.idxBij i) = i := h.idxBij_leftInverse_idxBij_symm _

theorem Perm.idxBij_symm_idxBij [BEq α] [LawfulBEq α] {xs ys : List α} (h : xs ~ ys)
    {i : Fin xs.length} : h.symm.idxBij (h.idxBij i) = i := h.idxBij_rightInverse_idxBij_symm _

theorem Perm.idxBij_injective [BEq α] [LawfulBEq α] {xs ys : List α} (h : xs ~ ys) :
    h.idxBij.Injective := h.idxBij_rightInverse_idxBij_symm.injective

theorem Perm.idxBij_surjective [BEq α] [LawfulBEq α] {xs ys : List α} (h : xs ~ ys) :
    h.idxBij.Surjective := h.idxBij_symm_rightInverse_idxBij.surjective

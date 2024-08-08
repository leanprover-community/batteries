/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad, Mario Carneiro
-/
import Batteries.Tactic.Alias
import Batteries.Data.List.Pairwise

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

@[simp, refl] protected theorem Perm.refl : ∀ l : List α, l ~ l
  | [] => .nil
  | x :: xs => (Perm.refl xs).cons x

protected theorem Perm.rfl {l : List α} : l ~ l := .refl _

theorem Perm.of_eq (h : l₁ = l₂) : l₁ ~ l₂ := h ▸ .rfl

protected theorem Perm.symm {l₁ l₂ : List α} (h : l₁ ~ l₂) : l₂ ~ l₁ := by
  induction h with
  | nil => exact nil
  | cons _ _ ih => exact cons _ ih
  | swap => exact swap ..
  | trans _ _ ih₁ ih₂ => exact trans ih₂ ih₁

theorem perm_comm {l₁ l₂ : List α} : l₁ ~ l₂ ↔ l₂ ~ l₁ := ⟨Perm.symm, Perm.symm⟩

theorem Perm.swap' (x y : α) {l₁ l₂ : List α} (p : l₁ ~ l₂) : y :: x :: l₁ ~ x :: y :: l₂ :=
  (swap ..).trans <| p.cons _ |>.cons _

/--
Similar to `Perm.recOn`, but the `swap` case is generalized to `Perm.swap'`,
where the tail of the lists are not necessarily the same.
-/
@[elab_as_elim] theorem Perm.recOnSwap'
    {motive : (l₁ : List α) → (l₂ : List α) → l₁ ~ l₂ → Prop} {l₁ l₂ : List α} (p : l₁ ~ l₂)
    (nil : motive [] [] .nil)
    (cons : ∀ x {l₁ l₂}, (h : l₁ ~ l₂) → motive l₁ l₂ h → motive (x :: l₁) (x :: l₂) (.cons x h))
    (swap' : ∀ x y {l₁ l₂}, (h : l₁ ~ l₂) → motive l₁ l₂ h →
      motive (y :: x :: l₁) (x :: y :: l₂) (.swap' _ _ h))
    (trans : ∀ {l₁ l₂ l₃}, (h₁ : l₁ ~ l₂) → (h₂ : l₂ ~ l₃) → motive l₁ l₂ h₁ → motive l₂ l₃ h₂ →
      motive l₁ l₃ (.trans h₁ h₂)) : motive l₁ l₂ p :=
  have motive_refl l : motive l l (.refl l) :=
    List.recOn l nil fun x xs ih => cons x (.refl xs) ih
  Perm.recOn p nil cons (fun x y l => swap' x y (.refl l) (motive_refl l)) trans

theorem Perm.eqv (α) : Equivalence (@Perm α) := ⟨.refl, .symm, .trans⟩

instance isSetoid (α) : Setoid (List α) := .mk Perm (Perm.eqv α)

theorem Perm.mem_iff {a : α} {l₁ l₂ : List α} (p : l₁ ~ l₂) : a ∈ l₁ ↔ a ∈ l₂ := by
  induction p with
  | nil => rfl
  | cons _ _ ih => simp only [mem_cons, ih]
  | swap => simp only [mem_cons, or_left_comm]
  | trans _ _ ih₁ ih₂ => simp only [ih₁, ih₂]

theorem Perm.subset {l₁ l₂ : List α} (p : l₁ ~ l₂) : l₁ ⊆ l₂ := fun _ => p.mem_iff.mp

theorem Perm.append_right {l₁ l₂ : List α} (t₁ : List α) (p : l₁ ~ l₂) : l₁ ++ t₁ ~ l₂ ++ t₁ := by
  induction p with
  | nil => rfl
  | cons _ _ ih => exact cons _ ih
  | swap => exact swap ..
  | trans _ _ ih₁ ih₂ => exact trans ih₁ ih₂

theorem Perm.append_left {t₁ t₂ : List α} : ∀ l : List α, t₁ ~ t₂ → l ++ t₁ ~ l ++ t₂
  | [], p => p
  | x :: xs, p => (p.append_left xs).cons x

theorem Perm.append {l₁ l₂ t₁ t₂ : List α} (p₁ : l₁ ~ l₂) (p₂ : t₁ ~ t₂) : l₁ ++ t₁ ~ l₂ ++ t₂ :=
  (p₁.append_right t₁).trans (p₂.append_left l₂)

theorem Perm.append_cons (a : α) {h₁ h₂ t₁ t₂ : List α} (p₁ : h₁ ~ h₂) (p₂ : t₁ ~ t₂) :
    h₁ ++ a :: t₁ ~ h₂ ++ a :: t₂ := p₁.append (p₂.cons a)

@[simp] theorem perm_middle {a : α} : ∀ {l₁ l₂ : List α}, l₁ ++ a :: l₂ ~ a :: (l₁ ++ l₂)
  | [], _ => .refl _
  | b :: _, _ => (Perm.cons _ perm_middle).trans (swap a b _)

@[simp] theorem perm_append_singleton (a : α) (l : List α) : l ++ [a] ~ a :: l :=
  perm_middle.trans <| by rw [append_nil]

theorem perm_append_comm : ∀ {l₁ l₂ : List α}, l₁ ++ l₂ ~ l₂ ++ l₁
  | [], l₂ => by simp
  | a :: t, l₂ => (perm_append_comm.cons _).trans perm_middle.symm

theorem concat_perm (l : List α) (a : α) : concat l a ~ a :: l := by simp

theorem Perm.length_eq {l₁ l₂ : List α} (p : l₁ ~ l₂) : length l₁ = length l₂ := by
  induction p with
  | nil => rfl
  | cons _ _ ih => simp only [length_cons, ih]
  | swap => rfl
  | trans _ _ ih₁ ih₂ => simp only [ih₁, ih₂]

theorem Perm.eq_nil {l : List α} (p : l ~ []) : l = [] := eq_nil_of_length_eq_zero p.length_eq

theorem Perm.nil_eq {l : List α} (p : [] ~ l) : [] = l := p.symm.eq_nil.symm

@[simp] theorem perm_nil {l₁ : List α} : l₁ ~ [] ↔ l₁ = [] :=
  ⟨fun p => p.eq_nil, fun e => e ▸ .rfl⟩

@[simp] theorem nil_perm {l₁ : List α} : [] ~ l₁ ↔ l₁ = [] := perm_comm.trans perm_nil

theorem not_perm_nil_cons (x : α) (l : List α) : ¬[] ~ x :: l := (nomatch ·.symm.eq_nil)

@[simp] theorem reverse_perm : ∀ l : List α, reverse l ~ l
  | [] => .nil
  | a :: l => reverse_cons .. ▸ (perm_append_singleton _ _).trans ((reverse_perm l).cons a)

theorem perm_cons_append_cons {l l₁ l₂ : List α} (a : α) (p : l ~ l₁ ++ l₂) :
    a :: l ~ l₁ ++ a :: l₂ := (p.cons a).trans perm_middle.symm

@[simp] theorem perm_replicate {n : Nat} {a : α} {l : List α} :
    l ~ replicate n a ↔ l = replicate n a := by
  refine ⟨fun p => eq_replicate.2 ?_, fun h => h ▸ .rfl⟩
  exact ⟨p.length_eq.trans <| length_replicate .., fun _b m => eq_of_mem_replicate <| p.subset m⟩

@[simp] theorem replicate_perm {n : Nat} {a : α} {l : List α} :
    replicate n a ~ l ↔ replicate n a = l := (perm_comm.trans perm_replicate).trans eq_comm

@[simp] theorem perm_singleton {a : α} {l : List α} : l ~ [a] ↔ l = [a] := perm_replicate (n := 1)

@[simp] theorem singleton_perm {a : α} {l : List α} : [a] ~ l ↔ [a] = l := replicate_perm (n := 1)

alias ⟨Perm.eq_singleton,_⟩ := perm_singleton
alias ⟨Perm.singleton_eq,_⟩ := singleton_perm

theorem singleton_perm_singleton {a b : α} : [a] ~ [b] ↔ a = b := by simp

theorem perm_cons_erase [DecidableEq α] {a : α} {l : List α} (h : a ∈ l) : l ~ a :: l.erase a :=
  let ⟨_l₁, _l₂, _, e₁, e₂⟩ := exists_erase_eq h
  e₂ ▸ e₁ ▸ perm_middle

theorem Perm.filterMap (f : α → Option β) {l₁ l₂ : List α} (p : l₁ ~ l₂) :
    filterMap f l₁ ~ filterMap f l₂ := by
  induction p with
  | nil => simp
  | cons x _p IH => cases h : f x <;> simp [h, filterMap_cons, IH, Perm.cons]
  | swap x y l₂ => cases hx : f x <;> cases hy : f y <;> simp [hx, hy, filterMap_cons, swap]
  | trans _p₁ _p₂ IH₁ IH₂ => exact IH₁.trans IH₂

theorem Perm.map (f : α → β) {l₁ l₂ : List α} (p : l₁ ~ l₂) : map f l₁ ~ map f l₂ :=
  filterMap_eq_map f ▸ p.filterMap _

theorem Perm.pmap {p : α → Prop} (f : ∀ a, p a → β) {l₁ l₂ : List α} (p : l₁ ~ l₂) {H₁ H₂} :
    pmap f l₁ H₁ ~ pmap f l₂ H₂ := by
  induction p with
  | nil => simp
  | cons x _p IH => simp [IH, Perm.cons]
  | swap x y => simp [swap]
  | trans _p₁ p₂ IH₁ IH₂ => exact IH₁.trans (IH₂ (H₁ := fun a m => H₂ a (p₂.subset m)))

theorem Perm.filter (p : α → Bool) {l₁ l₂ : List α} (s : l₁ ~ l₂) :
    filter p l₁ ~ filter p l₂ := by rw [← filterMap_eq_filter]; apply s.filterMap

theorem filter_append_perm (p : α → Bool) (l : List α) :
    filter p l ++ filter (fun x => !p x) l ~ l := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    by_cases h : p x <;> simp [h]
    · exact ih.cons x
    · exact Perm.trans (perm_append_comm.trans (perm_append_comm.cons _)) (ih.cons x)

theorem exists_perm_sublist {l₁ l₂ l₂' : List α} (s : l₁ <+ l₂) (p : l₂ ~ l₂') :
    ∃ l₁', l₁' ~ l₁ ∧ l₁' <+ l₂' := by
  induction p generalizing l₁ with
  | nil => exact ⟨[], sublist_nil.mp s ▸ .rfl, nil_sublist _⟩
  | cons x _ IH =>
    match s with
    | .cons _ s => let ⟨l₁', p', s'⟩ := IH s; exact ⟨l₁', p', s'.cons _⟩
    | .cons₂ _ s => let ⟨l₁', p', s'⟩ := IH s; exact ⟨x :: l₁', p'.cons x, s'.cons₂ _⟩
  | swap x y l' =>
    match s with
    | .cons _ (.cons _ s) => exact ⟨_, .rfl, (s.cons _).cons _⟩
    | .cons _ (.cons₂ _ s) => exact ⟨x :: _, .rfl, (s.cons _).cons₂ _⟩
    | .cons₂ _ (.cons _ s) => exact ⟨y :: _, .rfl, (s.cons₂ _).cons _⟩
    | .cons₂ _ (.cons₂ _ s) => exact ⟨x :: y :: _, .swap .., (s.cons₂ _).cons₂ _⟩
  | trans _ _ IH₁ IH₂ =>
    let ⟨m₁, pm, sm⟩ := IH₁ s
    let ⟨r₁, pr, sr⟩ := IH₂ sm
    exact ⟨r₁, pr.trans pm, sr⟩

theorem Perm.sizeOf_eq_sizeOf [SizeOf α] {l₁ l₂ : List α} (h : l₁ ~ l₂) :
    sizeOf l₁ = sizeOf l₂ := by
  induction h with
  | nil => rfl
  | cons _ _ h_sz₁₂ => simp [h_sz₁₂]
  | swap => simp [Nat.add_left_comm]
  | trans _ _ h_sz₁₂ h_sz₂₃ => simp [h_sz₁₂, h_sz₂₃]

section Subperm

theorem nil_subperm {l : List α} : [] <+~ l := ⟨[], Perm.nil, by simp⟩

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

@[simp] theorem singleton_subperm_iff {α} {l : List α} {a : α} : [a] <+~ l ↔ a ∈ l := by
  refine ⟨fun ⟨s, hla, h⟩ => ?_, fun h => ⟨[a], .rfl, singleton_sublist.mpr h⟩⟩
  rwa [perm_singleton.mp hla, singleton_sublist] at h

end Subperm

theorem Sublist.exists_perm_append {l₁ l₂ : List α} : l₁ <+ l₂ → ∃ l, l₂ ~ l₁ ++ l
  | Sublist.slnil => ⟨nil, .rfl⟩
  | Sublist.cons a s =>
    let ⟨l, p⟩ := Sublist.exists_perm_append s
    ⟨a :: l, (p.cons a).trans perm_middle.symm⟩
  | Sublist.cons₂ a s =>
    let ⟨l, p⟩ := Sublist.exists_perm_append s
    ⟨l, p.cons a⟩

theorem Perm.countP_eq (p : α → Bool) {l₁ l₂ : List α} (s : l₁ ~ l₂) :
    countP p l₁ = countP p l₂ := by
  simp only [countP_eq_length_filter]
  exact (s.filter _).length_eq

theorem Subperm.countP_le (p : α → Bool) {l₁ l₂ : List α} : l₁ <+~ l₂ → countP p l₁ ≤ countP p l₂
  | ⟨_l, p', s⟩ => p'.countP_eq p ▸ s.countP_le p

theorem Perm.countP_congr {l₁ l₂ : List α} (s : l₁ ~ l₂) {p p' : α → Bool}
    (hp : ∀ x ∈ l₁, p x = p' x) : l₁.countP p = l₂.countP p' := by
  rw [← s.countP_eq p']
  clear s
  induction l₁ with
  | nil => rfl
  | cons y s hs =>
    simp only [mem_cons, forall_eq_or_imp] at hp
    simp only [countP_cons, hs hp.2, hp.1]

theorem countP_eq_countP_filter_add (l : List α) (p q : α → Bool) :
    l.countP p = (l.filter q).countP p + (l.filter fun a => !q a).countP p :=
  countP_append .. ▸ Perm.countP_eq _ (filter_append_perm _ _).symm

theorem Perm.count_eq [DecidableEq α] {l₁ l₂ : List α} (p : l₁ ~ l₂) (a) :
    count a l₁ = count a l₂ := p.countP_eq _

theorem Subperm.count_le [DecidableEq α] {l₁ l₂ : List α} (s : l₁ <+~ l₂) (a) :
    count a l₁ ≤ count a l₂ := s.countP_le _

theorem Perm.foldl_eq' {f : β → α → β} {l₁ l₂ : List α} (p : l₁ ~ l₂)
    (comm : ∀ x ∈ l₁, ∀ y ∈ l₁, ∀ (z), f (f z x) y = f (f z y) x)
    (init) : foldl f init l₁ = foldl f init l₂ := by
  induction p using recOnSwap' generalizing init with
  | nil => simp
  | cons x _p IH =>
    simp only [foldl]
    apply IH; intros; apply comm <;> exact .tail _ ‹_›
  | swap' x y _p IH =>
    simp only [foldl]
    rw [comm x (.tail _ <| .head _) y (.head _)]
    apply IH; intros; apply comm <;> exact .tail _ (.tail _ ‹_›)
  | trans p₁ _p₂ IH₁ IH₂ =>
    refine (IH₁ comm init).trans (IH₂ ?_ _)
    intros; apply comm <;> apply p₁.symm.subset <;> assumption

theorem Perm.rec_heq {β : List α → Sort _} {f : ∀ a l, β l → β (a :: l)} {b : β []} {l l' : List α}
    (hl : l ~ l') (f_congr : ∀ {a l l' b b'}, l ~ l' → HEq b b' → HEq (f a l b) (f a l' b'))
    (f_swap : ∀ {a a' l b}, HEq (f a (a' :: l) (f a' l b)) (f a' (a :: l) (f a l b))) :
    HEq (@List.rec α β b f l) (@List.rec α β b f l') := by
  induction hl with
  | nil => rfl
  | cons a h ih => exact f_congr h ih
  | swap a a' l => exact f_swap
  | trans _h₁ _h₂ ih₁ ih₂ => exact ih₁.trans ih₂

/-- Lemma used to destruct perms element by element. -/
theorem perm_inv_core {a : α} {l₁ l₂ r₁ r₂ : List α} :
    l₁ ++ a :: r₁ ~ l₂ ++ a :: r₂ → l₁ ++ r₁ ~ l₂ ++ r₂ := by
  -- Necessary generalization for `induction`
  suffices ∀ s₁ s₂ (_ : s₁ ~ s₂) {l₁ l₂ r₁ r₂},
      l₁ ++ a :: r₁ = s₁ → l₂ ++ a :: r₂ = s₂ → l₁ ++ r₁ ~ l₂ ++ r₂ from (this _ _ · rfl rfl)
  intro s₁ s₂ p
  induction p using Perm.recOnSwap' with intro l₁ l₂ r₁ r₂ e₁ e₂
  | nil =>
    simp at e₁
  | cons x p IH =>
    cases l₁ <;> cases l₂ <;>
      dsimp at e₁ e₂ <;> injections <;> subst_vars
    · exact p
    · exact p.trans perm_middle
    · exact perm_middle.symm.trans p
    · exact (IH rfl rfl).cons _
  | swap' x y p IH =>
    obtain _ | ⟨y, _ | ⟨z, l₁⟩⟩ := l₁
      <;> obtain _ | ⟨u, _ | ⟨v, l₂⟩⟩ := l₂
      <;> dsimp at e₁ e₂ <;> injections <;> subst_vars
      <;> try exact p.cons _
    · exact (p.trans perm_middle).cons u
    · exact ((p.trans perm_middle).cons _).trans (swap _ _ _)
    · exact (perm_middle.symm.trans p).cons y
    · exact (swap _ _ _).trans ((perm_middle.symm.trans p).cons u)
    · exact (IH rfl rfl).swap' _ _
  | trans p₁ p₂ IH₁ IH₂ =>
    subst e₁ e₂
    obtain ⟨l₂, r₂, rfl⟩ := append_of_mem (a := a) (p₁.subset (by simp))
    exact (IH₁ rfl rfl).trans (IH₂ rfl rfl)

theorem Perm.cons_inv {a : α} {l₁ l₂ : List α} : a :: l₁ ~ a :: l₂ → l₁ ~ l₂ :=
  perm_inv_core (l₁ := []) (l₂ := [])

@[simp] theorem perm_cons (a : α) {l₁ l₂ : List α} : a :: l₁ ~ a :: l₂ ↔ l₁ ~ l₂ :=
  ⟨.cons_inv, .cons a⟩

theorem perm_append_left_iff {l₁ l₂ : List α} : ∀ l, l ++ l₁ ~ l ++ l₂ ↔ l₁ ~ l₂
  | [] => .rfl
  | a :: l => (perm_cons a).trans (perm_append_left_iff l)

theorem perm_append_right_iff {l₁ l₂ : List α} (l) : l₁ ++ l ~ l₂ ++ l ↔ l₁ ~ l₂ := by
  refine ⟨fun p => ?_, .append_right _⟩
  exact (perm_append_left_iff _).1 <| perm_append_comm.trans <| p.trans perm_append_comm

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
    have bm : b ∈ l₁ := p.subset <| mem_cons_self _ _
    have am : a ∈ r₂ := by
      simp only [find?, mem_cons] at h₂
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
  induction s₂ generalizing l₁ with simp [Nodup] at d
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

section DecidableEq

variable [DecidableEq α]

theorem Perm.erase (a : α) {l₁ l₂ : List α} (p : l₁ ~ l₂) : l₁.erase a ~ l₂.erase a :=
  if h₁ : a ∈ l₁ then
    have h₂ : a ∈ l₂ := p.subset h₁
    .cons_inv <| (perm_cons_erase h₁).symm.trans <| p.trans (perm_cons_erase h₂)
  else by
    have h₂ : a ∉ l₂ := mt p.mem_iff.2 h₁
    rw [erase_of_not_mem h₁, erase_of_not_mem h₂]; exact p

theorem subperm_cons_erase (a : α) (l : List α) : l <+~ a :: l.erase a :=
  if h : a ∈ l then
    (perm_cons_erase h).subperm
  else
    (erase_of_not_mem h).symm ▸ (sublist_cons_self _ _).subperm

theorem erase_subperm (a : α) (l : List α) : l.erase a <+~ l := (erase_sublist _ _).subperm

theorem Subperm.erase {l₁ l₂ : List α} (a : α) (h : l₁ <+~ l₂) : l₁.erase a <+~ l₂.erase a :=
  let ⟨l, hp, hs⟩ := h
  ⟨l.erase a, hp.erase _, hs.erase _⟩

theorem Perm.diff_right {l₁ l₂ : List α} (t : List α) (h : l₁ ~ l₂) : l₁.diff t ~ l₂.diff t := by
  induction t generalizing l₁ l₂ h with simp only [List.diff]
  | nil => exact h
  | cons x t ih =>
    simp only [elem_eq_mem, decide_eq_true_eq, Perm.mem_iff h]
    split
    · exact ih (h.erase _)
    · exact ih h

theorem Perm.diff_left (l : List α) {t₁ t₂ : List α} (h : t₁ ~ t₂) : l.diff t₁ = l.diff t₂ := by
  induction h generalizing l with try simp [List.diff]
  | cons x _ ih => apply ite_congr rfl <;> (intro; apply ih)
  | swap x y =>
    if h : x = y then
      simp [h]
    else
      simp [mem_erase_of_ne h, mem_erase_of_ne (Ne.symm h), erase_comm x y]
      split <;> simp [h]
  | trans => simp only [*]

theorem Perm.diff {l₁ l₂ t₁ t₂ : List α} (hl : l₁ ~ l₂) (ht : t₁ ~ t₂) : l₁.diff t₁ ~ l₂.diff t₂ :=
  ht.diff_left l₂ ▸ hl.diff_right _

theorem Subperm.diff_right {l₁ l₂ : List α} (h : l₁ <+~ l₂) (t : List α) :
    l₁.diff t <+~ l₂.diff t := by
  induction t generalizing l₁ l₂ h with simp [List.diff, elem_eq_mem, *]
  | cons x t ih =>
    split <;> rename_i hx1
    · simp [h.subset hx1]
      exact ih (h.erase _)
    · split
      · rw [← erase_of_not_mem hx1]
        exact ih (h.erase _)
      · exact ih h

theorem erase_cons_subperm_cons_erase (a b : α) (l : List α) :
    (a :: l).erase b <+~ a :: l.erase b := by
  if h : a = b then
    rw [h, erase_cons_head]; apply subperm_cons_erase
  else
    have : ¬(a == b) = true := by simp only [beq_false_of_ne h, not_false_eq_true]
    rw [erase_cons_tail this]

theorem subperm_cons_diff {a : α} {l₁ l₂ : List α} : (a :: l₁).diff l₂ <+~ a :: l₁.diff l₂ := by
  induction l₂ with
  | nil => exact ⟨a :: l₁, by simp [List.diff]⟩
  | cons b l₂ ih =>
    rw [diff_cons, diff_cons, ← diff_erase, ← diff_erase]
    exact Subperm.trans (.erase _ ih) (erase_cons_subperm_cons_erase ..)

theorem subset_cons_diff {a : α} {l₁ l₂ : List α} : (a :: l₁).diff l₂ ⊆ a :: l₁.diff l₂ :=
  subperm_cons_diff.subset

theorem cons_perm_iff_perm_erase {a : α} {l₁ l₂ : List α} :
    a :: l₁ ~ l₂ ↔ a ∈ l₂ ∧ l₁ ~ l₂.erase a := by
  refine ⟨fun h => ?_, fun ⟨m, h⟩ => (h.cons a).trans (perm_cons_erase m).symm⟩
  have : a ∈ l₂ := h.subset (mem_cons_self a l₁)
  exact ⟨this, (h.trans <| perm_cons_erase this).cons_inv⟩

theorem perm_iff_count {l₁ l₂ : List α} : l₁ ~ l₂ ↔ ∀ a, count a l₁ = count a l₂ := by
  refine ⟨Perm.count_eq, fun H => ?_⟩
  induction l₁ generalizing l₂ with
  | nil =>
    match l₂ with
    | nil => rfl
    | cons b l₂ =>
      specialize H b
      simp at H
  | cons a l₁ IH =>
    have : a ∈ l₂ := count_pos_iff_mem.mp (by rw [← H]; simp)
    refine ((IH fun b => ?_).cons a).trans (perm_cons_erase this).symm
    specialize H b
    rw [(perm_cons_erase this).count_eq] at H
    by_cases h : b = a <;> simpa [h] using H

/-- The list version of `add_tsub_cancel_of_le` for multisets. -/
theorem subperm_append_diff_self_of_count_le {l₁ l₂ : List α}
    (h : ∀ x ∈ l₁, count x l₁ ≤ count x l₂) : l₁ ++ l₂.diff l₁ ~ l₂ := by
  induction l₁ generalizing l₂ with
  | nil => simp
  | cons hd tl IH =>
    have : hd ∈ l₂ := by
      rw [← count_pos_iff_mem]
      exact Nat.lt_of_lt_of_le (count_pos_iff_mem.mpr (.head _)) (h hd (.head _))
    have := perm_cons_erase this
    refine Perm.trans ?_ this.symm
    rw [cons_append, diff_cons, perm_cons]
    refine IH fun x hx => ?_
    specialize h x (.tail _ hx)
    rw [perm_iff_count.mp this] at h
    if hx : x = hd then subst hd; simpa [Nat.succ_le_succ_iff] using h
    else simpa [hx] using h

/-- The list version of `Multiset.le_iff_count`. -/
theorem subperm_ext_iff {l₁ l₂ : List α} : l₁ <+~ l₂ ↔ ∀ x ∈ l₁, count x l₁ ≤ count x l₂ := by
  refine ⟨fun h x _ => h.count_le x, fun h => ?_⟩
  have : l₁ <+~ l₂.diff l₁ ++ l₁ := (subperm_append_right l₁).mpr nil_subperm
  refine this.trans (Perm.subperm ?_)
  exact perm_append_comm.trans (subperm_append_diff_self_of_count_le h)

theorem isSubperm_iff {l₁ l₂ : List α} : l₁.isSubperm l₂ ↔ l₁ <+~ l₂ := by
  simp [isSubperm, subperm_ext_iff]

instance decidableSubperm : DecidableRel ((· <+~ ·) : List α → List α → Prop) := fun _ _ =>
  decidable_of_iff _ isSubperm_iff

theorem Subperm.cons_left {l₁ l₂ : List α} (h : l₁ <+~ l₂) (x : α) (hx : count x l₁ < count x l₂) :
    x :: l₁ <+~ l₂ := by
  rw [subperm_ext_iff] at h ⊢
  intro y hy
  if hy' : y = x then
    subst x; simpa using Nat.succ_le_of_lt hx
  else
    rw [count_cons_of_ne hy']
    refine h y ?_
    simpa [hy'] using hy

theorem isPerm_iff : ∀ {l₁ l₂ : List α}, l₁.isPerm l₂ ↔ l₁ ~ l₂
  | [], [] => by simp [isPerm, isEmpty]
  | [], _ :: _ => by simp [isPerm, isEmpty, Perm.nil_eq]
  | a :: l₁, l₂ => by simp [isPerm, isPerm_iff, cons_perm_iff_perm_erase]

instance decidablePerm (l₁ l₂ : List α) : Decidable (l₁ ~ l₂) := decidable_of_iff _ isPerm_iff

protected theorem Perm.insert (a : α) {l₁ l₂ : List α} (p : l₁ ~ l₂) :
    l₁.insert a ~ l₂.insert a := by
  if h : a ∈ l₁ then
    simp [h, p.subset h, p]
  else
    have := p.cons a
    simpa [h, mt p.mem_iff.2 h] using this

theorem perm_insert_swap (x y : α) (l : List α) :
    List.insert x (List.insert y l) ~ List.insert y (List.insert x l) := by
  by_cases xl : x ∈ l <;> by_cases yl : y ∈ l <;> simp [xl, yl]
  if xy : x = y then simp [xy] else
  simp [List.insert, xl, yl, xy, Ne.symm xy]
  constructor

theorem perm_insertNth {α} (x : α) (l : List α) {n} (h : n ≤ l.length) :
    insertNth n x l ~ x :: l := by
  induction l generalizing n with
  | nil =>
    cases n with
    | zero => rfl
    | succ => cases h
  | cons _ _ ih =>
    cases n with
    | zero => simp [insertNth]
    | succ =>
      simp only [insertNth, modifyNthTail]
      refine .trans (.cons _ (ih (Nat.le_of_succ_le_succ h))) (.swap ..)

theorem Perm.union_right {l₁ l₂ : List α} (t₁ : List α) (h : l₁ ~ l₂) : l₁ ∪ t₁ ~ l₂ ∪ t₁ := by
  induction h with
  | nil => rfl
  | cons a _ ih => exact ih.insert a
  | swap => apply perm_insert_swap
  | trans _ _ ih_1 ih_2 => exact ih_1.trans ih_2

theorem Perm.union_left (l : List α) {t₁ t₂ : List α} (h : t₁ ~ t₂) : l ∪ t₁ ~ l ∪ t₂ := by
  induction l with
  | nil => simp only [nil_union, h]
  | cons _ _ ih => simp only [cons_union, Perm.insert _ ih]

theorem Perm.union {l₁ l₂ t₁ t₂ : List α} (p₁ : l₁ ~ l₂) (p₂ : t₁ ~ t₂) : l₁ ∪ t₁ ~ l₂ ∪ t₂ :=
  (p₁.union_right t₁).trans (p₂.union_left l₂)

theorem Perm.inter_right {l₁ l₂ : List α} (t₁ : List α) : l₁ ~ l₂ → l₁ ∩ t₁ ~ l₂ ∩ t₁ := .filter _

theorem Perm.inter_left (l : List α) {t₁ t₂ : List α} (p : t₁ ~ t₂) : l ∩ t₁ = l ∩ t₂ :=
  filter_congr fun a _ => by simpa using p.mem_iff (a := a)

theorem Perm.inter {l₁ l₂ t₁ t₂ : List α} (p₁ : l₁ ~ l₂) (p₂ : t₁ ~ t₂) : l₁ ∩ t₁ ~ l₂ ∩ t₂ :=
  p₂.inter_left l₂ ▸ p₁.inter_right t₁

end DecidableEq

theorem Perm.pairwise_iff {R : α → α → Prop} (S : ∀ {x y}, R x y → R y x) :
    ∀ {l₁ l₂ : List α} (_p : l₁ ~ l₂), Pairwise R l₁ ↔ Pairwise R l₂ :=
  suffices ∀ {l₁ l₂}, l₁ ~ l₂ → Pairwise R l₁ → Pairwise R l₂
    from fun p => ⟨this p, this p.symm⟩
  fun {l₁ l₂} p d => by
    induction d generalizing l₂ with
    | nil => rw [← p.nil_eq]; constructor
    | cons h _ IH =>
      have : _ ∈ l₂ := p.subset (mem_cons_self _ _)
      obtain ⟨s₂, t₂, rfl⟩ := append_of_mem this
      have p' := (p.trans perm_middle).cons_inv
      refine (pairwise_middle S).2 (pairwise_cons.2 ⟨fun b m => ?_, IH p'⟩)
      exact h _ (p'.symm.subset m)

theorem Pairwise.perm {R : α → α → Prop} {l l' : List α} (hR : l.Pairwise R) (hl : l ~ l')
    (hsymm : ∀ {x y}, R x y → R y x) : l'.Pairwise R := (hl.pairwise_iff hsymm).mp hR

theorem Perm.pairwise {R : α → α → Prop} {l l' : List α} (hl : l ~ l') (hR : l.Pairwise R)
    (hsymm : ∀ {x y}, R x y → R y x) : l'.Pairwise R := hR.perm hl hsymm

theorem Perm.nodup_iff {l₁ l₂ : List α} : l₁ ~ l₂ → (Nodup l₁ ↔ Nodup l₂) :=
  Perm.pairwise_iff <| @Ne.symm α

theorem Perm.join {l₁ l₂ : List (List α)} (h : l₁ ~ l₂) : l₁.join ~ l₂.join := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simp only [join_cons, perm_append_left_iff, ih]
  | swap => simp only [join_cons, ← append_assoc, perm_append_right_iff]; exact perm_append_comm ..
  | trans _ _ ih₁ ih₂ => exact trans ih₁ ih₂

theorem Perm.bind_right {l₁ l₂ : List α} (f : α → List β) (p : l₁ ~ l₂) : l₁.bind f ~ l₂.bind f :=
  (p.map _).join

theorem Perm.join_congr :
    ∀ {l₁ l₂ : List (List α)} (_ : List.Forall₂ (· ~ ·) l₁ l₂), l₁.join ~ l₂.join
  | _, _, .nil => .rfl
  | _ :: _, _ :: _, .cons h₁ h₂ => h₁.append (Perm.join_congr h₂)

theorem Perm.eraseP (f : α → Bool) {l₁ l₂ : List α}
    (H : Pairwise (fun a b => f a → f b → False) l₁) (p : l₁ ~ l₂) : eraseP f l₁ ~ eraseP f l₂ := by
  induction p with
  | nil => simp
  | cons a p IH =>
    if h : f a then simp [h, p]
    else simp [h]; exact IH (pairwise_cons.1 H).2
  | swap a b l =>
    by_cases h₁ : f a <;> by_cases h₂ : f b <;> simp [h₁, h₂]
    · cases (pairwise_cons.1 H).1 _ (mem_cons.2 (Or.inl rfl)) h₂ h₁
    · apply swap
  | trans p₁ _ IH₁ IH₂ =>
    refine (IH₁ H).trans (IH₂ ((p₁.pairwise_iff ?_).1 H))
    exact fun h h₁ h₂ => h h₂ h₁

theorem perm_merge (s : α → α → Bool) (l r) : merge s l r ~ l ++ r := by
  match l, r with
  | [], r => simp
  | l, [] => simp
  | a::l, b::r =>
    rw [cons_merge_cons]
    split
    · apply Perm.trans ((perm_cons a).mpr (perm_merge s l (b::r)))
      simp [cons_append]
    · apply Perm.trans ((perm_cons b).mpr (perm_merge s (a::l) r))
      simp [cons_append]
      apply Perm.trans (Perm.swap ..)
      apply Perm.cons
      apply perm_cons_append_cons
      exact Perm.rfl

theorem Perm.merge (s₁ s₂ : α → α → Bool) (hl : l₁ ~ l₂) (hr : r₁ ~ r₂) :
    merge s₁ l₁ r₁ ~ merge s₂ l₂ r₂ :=
  Perm.trans (perm_merge ..) <| Perm.trans (Perm.append hl hr) <| Perm.symm (perm_merge ..)

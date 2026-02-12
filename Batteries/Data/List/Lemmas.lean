/-
Copyright (c) 2014 Parikshit Khanna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Parikshit Khanna, Jeremy Avigad, Leonardo de Moura, Floris van Doorn, Mario Carneiro
-/
module

public import Batteries.Control.ForInStep.Lemmas
public import Batteries.Data.List.Basic

@[expose] public section

namespace List

instance instNeZeroNatLengthCons {a : α} {l : List α} : NeZero (a :: l).length :=
  ⟨Nat.succ_ne_zero _⟩

/-! ### count -/

theorem count_getElem_take_succ [BEq α] [EquivBEq α] {xs : List α}
    {i : Nat} {hi} : (xs.take (i + 1)).count xs[i] = (xs.take i).count xs[i] + 1 := by
  grind [take_append_getElem]

theorem count_getElem_take_lt_count [BEq α] [EquivBEq α] {xs : List α}
    {i : Nat} {hi} : (xs.take i).count (xs[i]'hi) < xs.count xs[i] :=
  Nat.lt_of_succ_le (Nat.le_trans (Nat.le_of_eq count_getElem_take_succ.symm) <|
    (take_sublist _ _).count_le _)

/-! ### zip -/

attribute [grind =] zip_nil_left zip_nil_right zip_cons_cons

/-! ### zipIdx -/

attribute [grind =] zipIdx_nil zipIdx_cons

/-! ### toArray-/

@[deprecated List.getElem_toArray (since := "2025-09-11")]
theorem getElem_mk {xs : List α} {i : Nat} (h : i < xs.length) :
    (Array.mk xs)[i] = xs[i] := List.getElem_toArray h

/-! ### next? -/

@[simp, grind =] theorem next?_nil : @next? α [] = none := rfl
@[simp, grind =] theorem next?_cons (a l) : @next? α (a :: l) = some (a, l) := rfl

/-! ### dropLast -/

theorem dropLast_eq_eraseIdx {xs : List α} {i : Nat} (last_idx : i + 1 = xs.length) :
    xs.dropLast = List.eraseIdx xs i := by
  ext
  grind

/-! ### set -/

theorem set_eq_modify (a : α) : ∀ n (l : List α), l.set n a = l.modify n (fun _ => a)
  | 0, l => by cases l <;> rfl
  | _+1, [] => rfl
  | _+1, _ :: _ => congrArg (cons _) (set_eq_modify _ _ _)

theorem set_eq_take_cons_drop (a : α) {n l} (h : n < length l) :
    set l n a = take n l ++ a :: drop (n + 1) l := by
  rw [set_eq_modify, modify_eq_take_cons_drop h]

theorem modify_eq_set_getElem? (f : α → α) :
    ∀ n (l : List α), l.modify n f = ((fun a => l.set n (f a)) <$> l[n]?).getD l
  | 0, l => by cases l <;> simp
  | _+1, [] => rfl
  | n+1, b :: l =>
    (congrArg (cons _) (modify_eq_set_getElem? ..)).trans <| by cases h : l[n]? <;> simp [h]

@[deprecated (since := "2025-02-15")] alias modify_eq_set_get? := modify_eq_set_getElem?

theorem modify_eq_set_get (f : α → α) {n} {l : List α} (h) :
    l.modify n f = l.set n (f (l.get ⟨n, h⟩)) := by
  rw [modify_eq_set_getElem?, getElem?_eq_getElem h]; rfl

theorem getElem?_set_eq_of_lt (a : α) {n} {l : List α} (h : n < length l) :
    (set l n a)[n]? = some a := by rw [getElem?_set_self', getElem?_eq_getElem h]; rfl

theorem getElem?_set_of_lt (a : α) {m n} (l : List α) (h : n < length l) :
    (set l m a)[n]? = if m = n then some a else l[n]? := by
  simp [getElem?_set', getElem?_eq_getElem h]

@[deprecated (since := "2025-02-15")] alias get?_set_of_lt := getElem?_set_of_lt

theorem getElem?_set_of_lt' (a : α) {m n} (l : List α) (h : m < length l) :
    (set l m a)[n]? = if m = n then some a else l[n]? := by
  simp [getElem?_set]; split <;> subst_vars <;> simp [*]

@[deprecated (since := "2025-02-15")] alias get?_set_of_lt' := getElem?_set_of_lt'

/-! ### tail -/

theorem length_tail_add_one (l : List α) (h : 0 < length l) :
    (length (tail l)) + 1 = length l := by grind

/-! ### eraseP -/

@[simp] theorem extractP_eq_find?_eraseP
    (l : List α) : extractP p l = (find? p l, eraseP p l) := by
  suffices ∀ (acc) (xs) (h : l = acc.toList ++ xs),
      extractP.go p l xs acc = (xs.find? p, acc.toList ++ xs.eraseP p) from this #[] _  rfl
  intros
  fun_induction extractP.go with grind

/-! ### erase -/

theorem erase_eq_self_iff_forall_bne [BEq α] (a : α) (xs : List α) :
    xs.erase a = xs ↔ ∀ (x : α), x ∈ xs → ¬x == a := by
  rw [erase_eq_eraseP', eraseP_eq_self_iff]

/-! ### findIdx? -/

@[deprecated findIdx_eq_getD_findIdx? (since := "2025-11-06")]
theorem findIdx_eq_findIdx? (p : α → Bool) (l : List α) :
    l.findIdx p = (match l.findIdx? p with | some i => i | none => l.length) := by
  rw [findIdx_eq_getD_findIdx?]
  cases findIdx? p l <;> rfl

/-! ### replaceF -/

theorem replaceF_nil : [].replaceF p = [] := rfl

theorem replaceF_cons (a : α) (l : List α) :
    (a :: l).replaceF p = match p a with
      | none => a :: replaceF p l
      | some a' => a' :: l := rfl

theorem replaceF_cons_of_some {l : List α} (p) (h : p a = some a') :
    (a :: l).replaceF p = a' :: l := by
  simp [h]

theorem replaceF_cons_of_none {l : List α} (p) (h : p a = none) :
    (a :: l).replaceF p = a :: l.replaceF p := by simp [h]

theorem replaceF_of_forall_none {l : List α} (h : ∀ a, a ∈ l → p a = none) : l.replaceF p = l := by
  induction l with
  | nil => rfl
  | cons _ _ ih => simp [h _ (.head ..), ih (forall_mem_cons.1 h).2]

theorem exists_of_replaceF : ∀ {l : List α} {a a'} (_ : a ∈ l) (_ : p a = some a'),
    ∃ a a' l₁ l₂,
      (∀ b ∈ l₁, p b = none) ∧ p a = some a' ∧ l = l₁ ++ a :: l₂ ∧ l.replaceF p = l₁ ++ a' :: l₂
  | b :: l, _, _, al, pa =>
    match pb : p b with
    | some b' => ⟨b, b', [], l, forall_mem_nil _, pb, by simp [pb]⟩
    | none =>
      match al with
      | .head .. => nomatch pb.symm.trans pa
      | .tail _ al =>
        let ⟨c, c', l₁, l₂, h₁, h₂, h₃, h₄⟩ := exists_of_replaceF al pa
        ⟨c, c', b::l₁, l₂, (forall_mem_cons ..).2 ⟨pb, h₁⟩,
          h₂, by rw [h₃, cons_append], by simp [pb, h₄]⟩

theorem exists_or_eq_self_of_replaceF (p) (l : List α) :
    l.replaceF p = l ∨ ∃ a a' l₁ l₂,
      (∀ b ∈ l₁, p b = none) ∧ p a = some a' ∧ l = l₁ ++ a :: l₂ ∧ l.replaceF p = l₁ ++ a' :: l₂ :=
  if h : ∃ a ∈ l, (p a).isSome then
    let ⟨_, ha, pa⟩ := h
    .inr (exists_of_replaceF ha (Option.get_mem pa))
  else
    .inl <| replaceF_of_forall_none fun a ha =>
      Option.not_isSome_iff_eq_none.1 fun h' => h ⟨a, ha, h'⟩

@[simp] theorem length_replaceF : length (replaceF f l) = length l := by
  induction l <;> simp [replaceF]; split <;> simp [*]

/-! ### disjoint -/

theorem disjoint_symm (d : Disjoint l₁ l₂) : Disjoint l₂ l₁ := fun _ i₂ i₁ => d i₁ i₂

theorem disjoint_comm : Disjoint l₁ l₂ ↔ Disjoint l₂ l₁ := ⟨disjoint_symm, disjoint_symm⟩

theorem disjoint_left : Disjoint l₁ l₂ ↔ ∀ ⦃a⦄, a ∈ l₁ → a ∉ l₂ := by simp [Disjoint]

theorem disjoint_right : Disjoint l₁ l₂ ↔ ∀ ⦃a⦄, a ∈ l₂ → a ∉ l₁ := disjoint_comm

theorem disjoint_iff_ne : Disjoint l₁ l₂ ↔ ∀ a ∈ l₁, ∀ b ∈ l₂, a ≠ b :=
  ⟨fun h _ al1 _ bl2 ab => h al1 (ab ▸ bl2), fun h _ al1 al2 => h _ al1 _ al2 rfl⟩

theorem disjoint_of_subset_left (ss : l₁ ⊆ l) (d : Disjoint l l₂) : Disjoint l₁ l₂ :=
  fun _ m => d (ss m)

theorem disjoint_of_subset_right (ss : l₂ ⊆ l) (d : Disjoint l₁ l) : Disjoint l₁ l₂ :=
  fun _ m m₁ => d m (ss m₁)

theorem disjoint_of_disjoint_cons_left {l₁ l₂} : Disjoint (a :: l₁) l₂ → Disjoint l₁ l₂ :=
  disjoint_of_subset_left (subset_cons_self _ _)

theorem disjoint_of_disjoint_cons_right {l₁ l₂} : Disjoint l₁ (a :: l₂) → Disjoint l₁ l₂ :=
  disjoint_of_subset_right (subset_cons_self _ _)

@[simp] theorem disjoint_nil_left (l : List α) : Disjoint [] l := fun _ => not_mem_nil.elim

@[simp] theorem disjoint_nil_right (l : List α) : Disjoint l [] := by
  rw [disjoint_comm]; exact disjoint_nil_left _

@[simp 1100] theorem singleton_disjoint : Disjoint [a] l ↔ a ∉ l := by simp [Disjoint]

@[simp 1100] theorem disjoint_singleton : Disjoint l [a] ↔ a ∉ l := by
  rw [disjoint_comm, singleton_disjoint]

@[simp] theorem disjoint_append_left : Disjoint (l₁ ++ l₂) l ↔ Disjoint l₁ l ∧ Disjoint l₂ l := by
  simp [Disjoint, or_imp, forall_and]

@[simp] theorem disjoint_append_right : Disjoint l (l₁ ++ l₂) ↔ Disjoint l l₁ ∧ Disjoint l l₂ :=
  disjoint_comm.trans <| by rw [disjoint_append_left]; simp [disjoint_comm]

@[simp] theorem disjoint_cons_left : Disjoint (a::l₁) l₂ ↔ (a ∉ l₂) ∧ Disjoint l₁ l₂ :=
  (disjoint_append_left (l₁ := [a])).trans <| by simp [singleton_disjoint]

@[simp] theorem disjoint_cons_right : Disjoint l₁ (a :: l₂) ↔ (a ∉ l₁) ∧ Disjoint l₁ l₂ :=
  disjoint_comm.trans <| by rw [disjoint_cons_left]; simp [disjoint_comm]

theorem disjoint_of_disjoint_append_left_left (d : Disjoint (l₁ ++ l₂) l) : Disjoint l₁ l :=
  (disjoint_append_left.1 d).1

theorem disjoint_of_disjoint_append_left_right (d : Disjoint (l₁ ++ l₂) l) : Disjoint l₂ l :=
  (disjoint_append_left.1 d).2

theorem disjoint_of_disjoint_append_right_left (d : Disjoint l (l₁ ++ l₂)) : Disjoint l l₁ :=
  (disjoint_append_right.1 d).1

theorem disjoint_of_disjoint_append_right_right (d : Disjoint l (l₁ ++ l₂)) : Disjoint l l₂ :=
  (disjoint_append_right.1 d).2

/-! ### union -/

section union

variable [BEq α]

theorem union_def (l₁ l₂ : List α)  : l₁ ∪ l₂ = foldr .insert l₂ l₁ := rfl

@[simp, grind =] theorem nil_union (l : List α) : nil ∪ l = l := by simp [List.union_def, foldr]

@[simp, grind =] theorem cons_union (a : α) (l₁ l₂ : List α) :
    (a :: l₁) ∪ l₂ = (l₁ ∪ l₂).insert a := by simp [List.union_def, foldr]

@[simp, grind =] theorem mem_union_iff [LawfulBEq α] {x : α} {l₁ l₂ : List α} :
    x ∈ l₁ ∪ l₂ ↔ x ∈ l₁ ∨ x ∈ l₂ := by induction l₁ <;> simp [*, or_assoc]

end union

/-! ### inter -/

theorem inter_def [BEq α] (l₁ l₂ : List α)  : l₁ ∩ l₂ = filter (elem · l₂) l₁ := rfl

@[simp, grind =] theorem mem_inter_iff [BEq α] [LawfulBEq α] {x : α} {l₁ l₂ : List α} :
    x ∈ l₁ ∩ l₂ ↔ x ∈ l₁ ∧ x ∈ l₂ := by
  cases l₁ <;> simp [List.inter_def, mem_filter]

/-! ### product -/

/-- List.prod satisfies a specification of cartesian product on lists. -/
@[simp]
theorem pair_mem_product {xs : List α} {ys : List β} {x : α} {y : β} :
    (x, y) ∈ product xs ys ↔ x ∈ xs ∧ y ∈ ys := by
  simp only [product, mem_map, Prod.mk.injEq,
    exists_eq_right_right, mem_flatMap, iff_self]

/-! ### monadic operations -/

theorem forIn_eq_bindList [Monad m] [LawfulMonad m]
    (f : α → β → m (ForInStep β)) (l : List α) (init : β) :
    forIn l init f = ForInStep.run <$> (ForInStep.yield init).bindList f l := by
  induction l generalizing init <;> simp [*]
  congr; ext (b | b) <;> simp

/-! ### diff -/

section Diff
variable [BEq α]

@[simp] theorem diff_nil (l : List α) : l.diff [] = l := rfl

variable [LawfulBEq α]

@[simp] theorem diff_cons (l₁ l₂ : List α) (a : α) : l₁.diff (a :: l₂) = (l₁.erase a).diff l₂ := by
  simp_all [List.diff, erase_of_not_mem]

theorem diff_cons_right (l₁ l₂ : List α) (a : α) : l₁.diff (a :: l₂) = (l₁.diff l₂).erase a := by
  apply Eq.symm; induction l₂ generalizing l₁ <;> simp [erase_comm, *]

theorem diff_erase (l₁ l₂ : List α) (a : α) : (l₁.diff l₂).erase a = (l₁.erase a).diff l₂ := by
  rw [← diff_cons_right, diff_cons]

@[simp] theorem nil_diff (l : List α) : [].diff l = [] := by
  induction l <;> simp [*, erase_of_not_mem]

theorem cons_diff (a : α) (l₁ l₂ : List α) :
    (a :: l₁).diff l₂ = if a ∈ l₂ then l₁.diff (l₂.erase a) else a :: l₁.diff l₂ := by
  induction l₂ generalizing l₁ with
  | nil => rfl
  | cons b l₂ ih =>
    by_cases h : a = b
    next => simp [*]
    next =>
      have := Ne.symm h
      simp[*]

theorem cons_diff_of_mem {a : α} {l₂ : List α} (h : a ∈ l₂) (l₁ : List α) :
    (a :: l₁).diff l₂ = l₁.diff (l₂.erase a) := by rw [cons_diff, if_pos h]

theorem cons_diff_of_not_mem {a : α} {l₂ : List α} (h : a ∉ l₂) (l₁ : List α) :
    (a :: l₁).diff l₂ = a :: l₁.diff l₂ := by rw [cons_diff, if_neg h]

theorem diff_eq_foldl : ∀ l₁ l₂ : List α, l₁.diff l₂ = foldl List.erase l₁ l₂
  | _, [] => rfl
  | l₁, a :: l₂ => (diff_cons l₁ l₂ a).trans (diff_eq_foldl _ _)

@[simp] theorem diff_append (l₁ l₂ l₃ : List α) : l₁.diff (l₂ ++ l₃) = (l₁.diff l₂).diff l₃ := by
  simp only [diff_eq_foldl, foldl_append]

theorem diff_sublist : ∀ l₁ l₂ : List α, l₁.diff l₂ <+ l₁
  | _, [] => .refl _
  | l₁, a :: l₂ =>
    calc
      l₁.diff (a :: l₂) = (l₁.erase a).diff l₂ := diff_cons ..
      _ <+ l₁.erase a := diff_sublist ..
      _ <+ l₁ := erase_sublist ..

theorem diff_subset (l₁ l₂ : List α) : l₁.diff l₂ ⊆ l₁ := (diff_sublist ..).subset

theorem mem_diff_of_mem {a : α} : ∀ {l₁ l₂ : List α}, a ∈ l₁ → a ∉ l₂ → a ∈ l₁.diff l₂
  | _, [], h₁, _ => h₁
  | l₁, b :: l₂, h₁, h₂ => by
    rw [diff_cons]
    exact mem_diff_of_mem ((mem_erase_of_ne <| ne_of_not_mem_cons h₂).2 h₁) (mt (.tail _) h₂)

theorem Sublist.diff_right : ∀ {l₁ l₂ l₃ : List α}, l₁ <+ l₂ → l₁.diff l₃ <+ l₂.diff l₃
  | _,  _, [], h => h
  | l₁, l₂, a :: l₃, h => by simp only [diff_cons, (h.erase _).diff_right]

theorem Sublist.erase_diff_erase_sublist {a : α} :
    ∀ {l₁ l₂ : List α}, l₁ <+ l₂ → (l₂.erase a).diff (l₁.erase a) <+ l₂.diff l₁
  | [], _, _ => erase_sublist
  | b :: l₁, l₂, h => by
    if heq : b = a then
      simp [heq]
    else
      simp [heq, erase_comm a]
      exact (erase_cons_head b _ ▸ h.erase b).erase_diff_erase_sublist

end Diff

/-! ### drop -/

theorem disjoint_take_drop : ∀ {l : List α}, l.Nodup → m ≤ n → Disjoint (l.take m) (l.drop n)
  | [], _, _ => by simp
  | x :: xs, hl, h => by
    cases m <;> cases n <;> simp only [disjoint_cons_left, drop, disjoint_nil_left,
      take]
    · case succ.zero => cases h
    · cases hl with | cons h₀ h₁ =>
      refine ⟨fun h => h₀ _ (mem_of_mem_drop h) rfl, ?_⟩
      exact disjoint_take_drop h₁ (Nat.le_of_succ_le_succ h)

/-! ### Pairwise -/

attribute [simp, grind ←] Pairwise.nil

@[grind →] protected theorem Pairwise.isChain (p : Pairwise R l) : IsChain R l := by
  induction p with
  | nil => grind
  | cons _ l => cases l with grind

@[grind =] theorem pairwise_cons_cons :
    Pairwise R (a :: b :: l) ↔ R a b ∧ Pairwise R (a :: l) ∧ Pairwise R (b :: l) := by
  grind [pairwise_cons]

/-! ### IsChain -/

@[deprecated (since := "2025-09-19")]
alias chain_cons := isChain_cons_cons

theorem rel_of_isChain_cons_cons (p : IsChain R (a :: b :: l)) : R a b :=
  (isChain_cons_cons.1 p).1

alias IsChain.rel := rel_of_isChain_cons_cons

@[deprecated (since := "2025-09-19")]
alias rel_of_chain_cons := rel_of_isChain_cons_cons

theorem isChain_of_isChain_cons (p : IsChain R (b :: l)) : IsChain R l := by grind [cases List]

alias IsChain.of_cons := isChain_of_isChain_cons

@[deprecated IsChain.of_cons (since := "2026-02-10")]
theorem isChain_cons_of_isChain_cons_cons : IsChain R (a :: b :: l) →
    IsChain R (b :: l) := IsChain.of_cons

@[deprecated (since := "2025-09-19")]
alias chain_of_chain_cons := isChain_cons_of_isChain_cons_cons

@[deprecated IsChain.of_cons (since := "2026-02-10")]
theorem isChain_of_isChain_cons_cons : IsChain R (a :: b :: l) →
    IsChain R l := IsChain.of_cons ∘ IsChain.of_cons

@[grind =>]
theorem IsChain.imp (H : ∀ ⦃a b : α⦄, R a b → S a b)
    (p : IsChain R l) : IsChain S l := by induction p with grind

@[deprecated (since := "2025-09-19")]
alias Chain.imp := IsChain.imp

theorem IsChain.cons_of_imp (h : ∀ c, R a c → R b c) :
    IsChain R (a :: l) → IsChain R (b :: l) := by grind [cases List]

@[deprecated (since := "2026-02-10")]
alias IsChain.cons_of_imp_of_cons := IsChain.cons_of_imp

theorem IsChain.cons_of_imp_of_imp (HRS : ∀ ⦃a b : α⦄, R a b → S a b)
    (Hab : ∀ ⦃c⦄, R a c → S b c) (h : IsChain R (a :: l)) : IsChain S (b :: l) := by
  grind [cases List]

@[deprecated (since := "2025-09-19")]
alias Chain.imp' := IsChain.cons_of_imp_of_imp

@[deprecated (since := "2025-09-19")]
protected alias Pairwise.chain := Pairwise.isChain

theorem isChain_iff_pairwise [Trans R R R] : IsChain R l ↔ Pairwise R l := by
  induction l with | nil => grind | cons a l IH => cases l with | nil => grind | cons b l =>
  simp only [isChain_cons_cons, IH, pairwise_cons, mem_cons, forall_eq_or_imp, and_congr_left_iff,
    iff_self_and, and_imp]
  exact flip <| fun _ => flip (Trans.trans · <| · · ·)

@[grind →] protected theorem IsChain.pairwise [Trans R R R] (c : IsChain R l) :
    Pairwise R l := isChain_iff_pairwise.mp c

theorem isChain_iff_getElem {l : List α} :
    IsChain R l ↔ ∀ (i : Nat) (_hi : i + 1 < l.length), R l[i] l[i + 1] := by
  induction l with | nil => grind | cons a l IH => cases l with | nil => grind | cons b l =>
  simp [IH, Nat.forall_lt_succ_left']

theorem IsChain.getElem {l : List α} (c : IsChain R l) (i : Nat) (hi : i + 1 < l.length) :
    R l[i] l[i + 1] := isChain_iff_getElem.mp c _ _

/-! ### range', range -/

theorem isChain_range' (s : Nat) : ∀ n step : Nat,
    IsChain (fun a b => b = a + step) (range' s n step)
  | 0, _ => .nil
  | 1, _ => .singleton _
  | n + 2, step => (isChain_range' (s + step) (n + 1) step).cons_cons rfl

@[deprecated isChain_range' (since := "2025-09-19")]
theorem chain_succ_range' (s n step : Nat) :
    IsChain (fun a b => b = a + step) (s :: range' (s + step) n step) := isChain_range'  _ (n + 1) _

theorem isChain_lt_range' (s n : Nat) (h : 0 < step) :
    IsChain (· < ·) (range' s n step) :=
  (isChain_range' s n step).imp fun | _, _, rfl => Nat.lt_add_of_pos_right h

@[deprecated isChain_lt_range' (since := "2025-09-19")]
theorem chain_lt_range' (s n : Nat) (h : 0 < step) :
    IsChain (· < ·) (s :: range' (s + step) n step) := isChain_lt_range' _ (n + 1) h

/-! ### foldrIdx -/

@[simp, grind =] theorem foldrIdx_nil : ([] : List α).foldrIdx f i s = i := rfl

@[simp, grind =] theorem foldrIdx_cons :
    (x :: xs : List α).foldrIdx f i s = f s x (foldrIdx f i xs (s + 1)) := rfl

@[grind =] theorem foldrIdx_start :
    (xs : List α).foldrIdx f i s = (xs : List α).foldrIdx (f <| · + s) i := by
  induction xs generalizing f s <;> grind

theorem foldrIdx_const : (xs : List α).foldrIdx (Function.const Nat f) i s = xs.foldr f i := by
  induction xs <;> grind

theorem foldrIdx_eq_foldr_zipIdx : (xs : List α).foldrIdx f i s =
    (xs.zipIdx s).foldr (fun ab => f ab.2 ab.1) i := by
  induction xs generalizing s <;> grind

/-! ### foldlIdx -/

@[simp, grind =] theorem foldlIdx_nil : ([] : List α).foldlIdx f i s = i := rfl

@[simp, grind =] theorem foldlIdx_cons :
    (x :: xs : List α).foldlIdx f i s = foldlIdx f (f s i x) xs (s + 1) := rfl

theorem foldlIdx_start :
    (xs : List α).foldlIdx f i s = (xs : List α).foldlIdx (f <| · + s) i := by
  induction xs generalizing f i s <;> grind [Function.comp_def]

theorem foldlIdx_const : (xs : List α).foldlIdx (Function.const Nat f) i s = xs.foldl f i := by
  induction xs generalizing i s <;> grind

theorem foldlIdx_eq_foldl_zipIdx : (xs : List α).foldlIdx f i s =
    (xs.zipIdx s).foldl (fun b ab => f ab.2 b ab.1) i := by
  induction xs generalizing i s <;> grind

/-! ### findIdxs -/

@[simp, grind =] theorem findIdxs_nil : ([] : List α).findIdxs p s = [] := rfl

@[simp, grind =] theorem findIdxs_cons :
    (x :: xs : List α).findIdxs p s =
    if p x then s :: xs.findIdxs p (s + 1) else xs.findIdxs p (s + 1) := by
  grind [findIdxs]

theorem findIdxs_singleton :
    [x].findIdxs p s = if p x then [s] else [] := by grind

theorem findIdxs_start :
    (xs : List α).findIdxs p s = (xs.findIdxs p).map (· + s) := by
  induction xs generalizing s <;> grind [map_inj_left]

theorem findIdxs_eq_filterMap_zipIdx : (xs : List α).findIdxs p s =
    ((xs.zipIdx s).filterMap fun ab => bif p ab.1 then ab.2 else none) := by
  induction xs generalizing s <;> grind

@[simp, grind =]
theorem mem_findIdxs_iff_getElem_sub_pos :
    i ∈ (xs : List α).findIdxs p s ↔ s ≤ i ∧
    ∃ (hix : i - s < xs.length), p xs[i - s] := by
  induction xs generalizing s <;> grind

theorem mem_findIdxs_iff_exists_getElem_pos :
    i ∈ (xs : List α).findIdxs p ↔ ∃ (hix : i < xs.length), p xs[i] := by grind

theorem mem_findIdxs_iff_pos_getElem (hi : i < (xs : List α).length) :
    i ∈ xs.findIdxs p ↔ p xs[i] := by grind

theorem ge_of_mem_findIdxs : ∀ y ∈ (xs : List α).findIdxs p s, s ≤ y := by grind

theorem lt_add_of_mem_findIdxs :
    ∀ y ∈ (xs : List α).findIdxs p s, y < xs.length + s := by grind

theorem findIdxs_eq_nil_iff :
    (xs : List α).findIdxs p s = [] ↔ ∀ x ∈ xs, p x = false := by
  induction xs generalizing s <;> grind

@[simp, grind =] theorem length_findIdxs : ((xs : List α).findIdxs p s).length = xs.countP p := by
  induction xs generalizing s <;> grind

@[simp, grind .]
theorem pairwise_findIdxs : ((xs : List α).findIdxs p s).Pairwise (· < ·) := by
  induction xs generalizing s <;> grind [pairwise_cons]

@[simp, grind .]
theorem isChain_findIdxs : ((xs : List α).findIdxs p s).IsChain (· < ·) :=
  pairwise_findIdxs.isChain

@[simp, grind .]
theorem nodup_findIdxs : ((xs : List α).findIdxs p s).Nodup := pairwise_findIdxs.imp (by grind)

@[simp, grind =]
theorem findIdxs_map :
    ((xs : List α).map f).findIdxs p s = xs.findIdxs (p ∘ f) s := by
  induction xs generalizing s <;> grind

@[simp, grind =]
theorem findIdxs_append :
    ((xs : List α) ++ ys).findIdxs p s = xs.findIdxs p s ++ ys.findIdxs p (s + xs.length) := by
  induction xs generalizing s <;> grind

@[simp, grind =]
theorem findIdxs_take :
    ((xs : List α).take n).findIdxs p s = (xs.findIdxs p s).take ((xs.take n).countP p) := by
  induction xs generalizing n s <;> cases n <;> grind [countP_eq_length_filter]

@[simp, grind =>]
theorem le_getElem_findIdxs (h : i < ((xs : List α).findIdxs p s).length) :
    s ≤ (xs.findIdxs p s)[i] := by grind [getElem_mem]

@[simp, grind =>]
theorem getElem_findIdxs_lt (h : i < ((xs : List α).findIdxs p s).length) :
    (xs.findIdxs p s)[i] < xs.length + s := by grind [getElem_mem]

theorem getElem_filter_eq_getElem_getElem_findIdxs_sub (s : Nat)
    (h : i < ((xs : List α).filter p).length) :
    (xs.filter p)[i] = xs[(xs.findIdxs p s)[i]'(by grind) - s]'(by grind) := by
  induction xs generalizing i s <;> grind

@[grind =>]
theorem getElem_filter_eq_getElem_getElem_findIdxs
    (h : i < ((xs : List α).filter p).length) :
    (xs.filter p)[i] = xs[(xs.findIdxs p)[i]'(by grind)]'(by grind) :=
  getElem_filter_eq_getElem_getElem_findIdxs_sub 0 h

theorem getElem_getElem_findIdxs_sub (s : Nat)
    (h : i < ((xs : List α).findIdxs p s).length) :
    haveI : (findIdxs p xs s)[i] - s < xs.length := by grind
    p xs[(xs.findIdxs p s)[i] - s] := by
  rw [← getElem_filter_eq_getElem_getElem_findIdxs_sub s] <;> grind

theorem getElem_getElem_findIdxs
    (h : i < ((xs : List α).findIdxs p).length) :
    haveI : (findIdxs p xs)[i] < xs.length := by grind
    p xs[(xs.findIdxs p)[i]] := getElem_getElem_findIdxs_sub 0 h

@[grind =]
theorem getElem_zero_findIdxs_eq_findIdx_add (h : 0 < ((xs : List α).findIdxs p s).length) :
    (xs.findIdxs p s)[0] = xs.findIdx p + s := by induction xs generalizing s <;> grind

@[simp]
theorem getElem_zero_findIdxs_eq_findIdx (h : 0 < ((xs : List α).findIdxs p).length) :
    (xs.findIdxs p)[0] = xs.findIdx p := getElem_zero_findIdxs_eq_findIdx_add h

@[grind =>]
theorem findIdx_add_mem_findIdxs (s : Nat)
    (h : (xs : List α).findIdx p < xs.length) : xs.findIdx p + s ∈ xs.findIdxs p s := by
  grind [mem_iff_getElem]

theorem findIdx_mem_findIdxs (h : (xs : List α).findIdx p < xs.length) :
    xs.findIdx p ∈ xs.findIdxs p := findIdx_add_mem_findIdxs 0 h

/-! ### findIdxsValues -/

@[grind =]
theorem findIdxsValues_eq_zip_filter_findIdxs :
    (xs : List α).findIdxsValues p s = (xs.findIdxs p s).zip (xs.filter p) := by
  induction xs generalizing s <;> grind [findIdxsValues]

@[simp, grind =]
theorem unzip_findIdxsValues :
    ((xs : List α).findIdxsValues p s).unzip = (xs.findIdxs p s, xs.filter p) := by
  grind [unzip_zip]

/-! ### findIdxNth  -/

@[simp, grind =] theorem findIdxNth_nil : ([] : List α).findIdxNth p n = 0 := rfl

@[grind =]
theorem findIdxNth_cons {a : α} :
    (a :: xs).findIdxNth p n =
    if n = 0 then if p a then 0 else xs.findIdxNth p 0 + 1
    else if p a then xs.findIdxNth p (n - 1) + 1
    else xs.findIdxNth p n + 1 := by
  have H : ∀ n s, findIdxNth.go (p : α → Bool) xs n s = (xs : List α).findIdxNth p n + s := by
    induction xs <;> grind [findIdxNth, findIdxNth.go, cases Nat]
  cases n <;> grind [findIdxNth, findIdxNth.go]

@[simp] theorem findIdxNth_cons_zero {a : α} :
    (a :: xs).findIdxNth p 0 = if p a then 0 else xs.findIdxNth p 0 + 1 := by grind

@[simp] theorem findIdxNth_cons_succ {a : α} :
    (a :: xs).findIdxNth p (n + 1) =
    if p a then xs.findIdxNth p n + 1 else xs.findIdxNth p (n + 1) + 1 := by grind

theorem findIdxNth_cons_of_neg {a : α} (h : p a = false) :
    (a :: xs).findIdxNth p n = xs.findIdxNth p n + 1 := by grind

theorem findIdxNth_cons_of_pos {a : α} (h : p a) :
    (a :: xs).findIdxNth p n = if n = 0 then 0 else
    xs.findIdxNth p (n - 1) + 1 := by grind

theorem findIdxNth_cons_zero_of_pos {a : α} (h : p a) :
    (a :: xs).findIdxNth p 0 = 0 := by grind

theorem findIdxNth_cons_succ_of_pos {a : α} (h : p a) :
    (a :: xs).findIdxNth p (n + 1) = xs.findIdxNth p n + 1 := by grind

theorem getElem_findIdxs_eq_findIdxNth_add {xs : List α} {h : n < (xs.findIdxs p s).length} :
    (xs.findIdxs p s)[n] = xs.findIdxNth p n + s := by
  induction xs generalizing n s <;> grind

@[grind =]
theorem getElem_findIdxs_eq_findIdxNth {xs : List α} {h : n < (xs.findIdxs p).length} :
    (xs.findIdxs p)[n] = xs.findIdxNth p n := getElem_findIdxs_eq_findIdxNth_add

theorem pos_findIdxNth_getElem {xs : List α} {h : xs.findIdxNth p n < xs.length} :
    p xs[xs.findIdxNth p n] := by induction xs generalizing n <;> grind

grind_pattern pos_findIdxNth_getElem => xs[xs.findIdxNth p n]

theorem findIdxNth_zero : (xs : List α).findIdxNth p 0 = xs.findIdx p := by
  induction xs <;> grind

@[grind _=_]
theorem findIdxNth_lt_length_iff {xs : List α} :
    xs.findIdxNth p n < xs.length ↔ n < xs.countP p := by
  induction xs generalizing n <;> grind

@[grind _=_]
theorem findIdxNth_eq_length_iff {xs : List α} :
    xs.findIdxNth p n = xs.length ↔ xs.countP p ≤ n := by
  induction xs generalizing n <;> grind

@[simp, grind .]
theorem findIdxNth_le_length {xs : List α} :
    xs.findIdxNth p n ≤ xs.length := (n.lt_or_ge (xs.countP p)).elim (by grind) (by grind)

theorem findIdxNth_lt_length_of_lt_countP {xs : List α} (h : n < xs.countP p) :
    xs.findIdxNth p n < xs.length := by grind

theorem findIdxNth_eq_length_of_ge_countP {xs : List α} :
    xs.countP p ≤ n → xs.findIdxNth p n = xs.length := by grind

theorem findIdxNth_le_findIdxNth_iff {xs : List α} :
    xs.findIdxNth p n ≤ xs.findIdxNth p m ↔ countP p xs ≤ m ∨ n ≤ m := by
  induction xs generalizing n m with
  | nil => grind
  | cons a xs IH => cases h : p a <;> cases n <;> cases m <;> simp [h, IH]

theorem findIdxNth_lt_findIdxNth_iff {xs : List α} :
    xs.findIdxNth p n < xs.findIdxNth p m ↔ n < xs.countP p ∧ n < m := by
  simp [← Nat.not_le, findIdxNth_le_findIdxNth_iff]

theorem findIdxNth_eq_findIdxNth_iff {xs : List α} :
    xs.findIdxNth p n = xs.findIdxNth p m ↔
    (xs.countP p ≤ m ∨ n ≤ m) ∧ (xs.countP p ≤ n ∨ m ≤ n) := by
  simp only [Nat.le_antisymm_iff, findIdxNth_le_findIdxNth_iff]

theorem findIdxNth_lt_findIdxNth_iff_of_lt_countP {xs : List α} (hn : n < xs.countP p) :
    xs.findIdxNth p n < xs.findIdxNth p m ↔ n < m := by
  grind [findIdxNth_lt_findIdxNth_iff]

theorem findIdxNth_mono {xs : List α} (hnm : n ≤ m):
    xs.findIdxNth p n ≤ xs.findIdxNth p m := by
  grind [Nat.le_iff_lt_or_eq, findIdxNth_lt_findIdxNth_iff, findIdxNth_eq_findIdxNth_iff]

theorem findIdxNth_eq_findIdxNth_iff_of_left_lt_countP {xs : List α} (hn : n < xs.countP p) :
    xs.findIdxNth p n = xs.findIdxNth p m ↔ n = m := by
  grind [findIdxNth_eq_findIdxNth_iff]

theorem findIdxNth_eq_findIdxNth_iff_of_right_lt_countP {xs : List α} (hm : m < xs.countP p) :
    xs.findIdxNth p n = xs.findIdxNth p m ↔ n = m := by
  grind [findIdxNth_eq_findIdxNth_iff]

theorem findIdxNth_eq_findIdxNth_of_ge_countP_ge_countP {xs : List α} (hn : xs.countP p ≤ n)
    (hm : xs.countP p ≤ m) : xs.findIdxNth p n = xs.findIdxNth p m := by
  grind [findIdxNth_eq_findIdxNth_iff]

/-! ### idxOf -/

@[simp] theorem eraseIdx_idxOf_eq_erase [BEq α] (a : α) (l : List α) :
    l.eraseIdx (l.idxOf a) = l.erase a := by
  induction l with grind

@[grind =] theorem idxOf_eq_getD_idxOf? [BEq α] (a : α) (l : List α) :
    l.idxOf a = (l.idxOf? a).getD l.length := by
  simp [idxOf, idxOf?, findIdx_eq_getD_findIdx?]

@[deprecated (since := "2025-11-06")]
alias idxOf_eq_idxOf? := idxOf_eq_getD_idxOf?

@[simp, grind =]
theorem getElem_idxOf [BEq α] [LawfulBEq α] {x : α} {xs : List α} (h : idxOf x xs < xs.length) :
    xs[xs.idxOf x] = x := by induction xs <;> grind

@[simp, grind =]
theorem Nodup.idxOf_getElem [BEq α] [LawfulBEq α] {xs : List α} (H : Nodup xs)
    (i : Nat) (h : i < xs.length) : idxOf xs[i] xs = i := by induction xs generalizing i <;> grind

/-! ### idxsOf -/

@[simp, grind =] theorem idxsOf_nil [BEq α] : ([] : List α).idxsOf x s = [] := rfl

@[simp, grind =] theorem idxsOf_cons [BEq α] : (x :: xs : List α).idxsOf y s =
    if x == y then s :: xs.idxsOf y (s + 1) else xs.idxsOf y (s + 1) := findIdxs_cons

theorem idxsOf_start [BEq α] :
    (xs : List α).idxsOf x s = (xs.idxsOf x).map (· + s) := findIdxs_start

theorem idxsOf_eq_filterMap_zipIdx [BEq α] : (xs : List α).idxsOf x s =
    ((xs.zipIdx s).filterMap fun ab => bif ab.1 == x then ab.2 else none) :=
  findIdxs_eq_filterMap_zipIdx

@[simp, grind =]
theorem mem_idxsOf_iff_getElem_sub_pos [BEq α] :
    i ∈ (xs : List α).idxsOf x s ↔ s ≤ i ∧
    ∃ (hix : i - s < xs.length), xs[i - s] == x := mem_findIdxs_iff_getElem_sub_pos

theorem mem_idxsOf_iff_exists_getElem_pos [BEq α] :
    i ∈ (xs : List α).idxsOf x ↔ ∃ (hix : i < xs.length), xs[i] == x := by grind

theorem mem_idxsOf_iff_getElem_pos [BEq α] (hi : i < (xs : List α).length) :
    i ∈ xs.idxsOf x ↔ xs[i] == x := by grind

theorem ge_of_mem_idxsOf [BEq α] : ∀ y ∈ (xs : List α).idxsOf x s, s ≤ y := by grind

theorem lt_add_of_mem_idxsOf [BEq α] :
    ∀ y ∈ (xs : List α).idxsOf x s, y < xs.length + s := by grind

theorem idxsOf_eq_nil_iff [BEq α] :
    (xs : List α).idxsOf x s = [] ↔ ∀ y ∈ xs, (y == x) = false := findIdxs_eq_nil_iff

@[simp, grind =] theorem length_idxsOf [BEq α] :
    ((xs : List α).idxsOf x s).length = xs.count x := length_findIdxs

@[simp, grind .]
theorem pairwise_idxsOf [BEq α] : ((xs : List α).idxsOf x s).Pairwise (· < ·) :=
  pairwise_findIdxs

@[simp, grind .]
theorem isChain_idxsOf [BEq α] : ((xs : List α).idxsOf x s).IsChain (· < ·) :=
  pairwise_idxsOf.isChain

@[simp, grind .]
theorem nodup_idxsOf [BEq α] : ((xs : List α).idxsOf x s).Nodup :=
  pairwise_idxsOf.imp (by grind)

@[simp, grind =]
theorem idxsOf_map [BEq α] {f : β → α} :
    ((xs : List β).map f).idxsOf x s = xs.findIdxs (f · == x) s := findIdxs_map

@[simp, grind =]
theorem idxsOf_append [BEq α] :
    ((xs : List α) ++ ys).idxsOf x s = xs.idxsOf x s ++ ys.idxsOf x (s + xs.length) :=
  findIdxs_append

@[simp, grind =]
theorem idxsOf_take [BEq α] :
    ((xs : List α).take n).idxsOf x s = (xs.idxsOf x s).take ((xs.take n).count x) :=
  findIdxs_take

@[simp, grind =>]
theorem le_getElem_idxsOf [BEq α] (h : i < ((xs : List α).idxsOf x s).length) :
    s ≤ (xs.idxsOf x s)[i] := by grind [getElem_mem]

@[simp, grind =>]
theorem getElem_idxsOf_lt [BEq α] (h : i < ((xs : List α).idxsOf x s).length) :
    (xs.idxsOf x s)[i] < xs.length + s := by grind [getElem_mem]

@[grind =>]
theorem getElem_getElem_idxsOf_sub [BEq α] (s : Nat)
    (h : i < ((xs : List α).idxsOf x s).length) :
    haveI : (idxsOf x xs s)[i] - s < xs.length := by grind
    xs[(xs.idxsOf x s)[i] - s] == x := getElem_getElem_findIdxs_sub s h

@[simp]
theorem getElem_getElem_idxsOf_sub_of_lawful [BEq α] [LawfulBEq α] (s : Nat)
    (h : i < ((xs : List α).idxsOf x s).length) :
    haveI : (idxsOf x xs s)[i] - s < xs.length := by grind
    xs[(xs.idxsOf x s)[i] - s] = x := by grind [getElem_getElem_idxsOf_sub]

theorem getElem_getElem_idxsOf [BEq α] (h : i < ((xs : List α).idxsOf x).length) :
    haveI : (idxsOf x xs)[i] < xs.length := by grind
    xs[(xs.idxsOf x)[i]] == x := by grind

@[simp]
theorem getElem_getElem_idxsOf_of_lawful [BEq α] [LawfulBEq α]
    (h : i < ((xs : List α).idxsOf x).length) :
    haveI : (idxsOf x xs)[i] < xs.length := by grind
  xs[(xs.idxsOf x)[i]] = x := by grind

@[grind =>]
theorem mem_idxsOf_getElem [BEq α] [EquivBEq α] (h : i < (xs : List α).length) :
    i ∈ xs.idxsOf xs[i] := by grind

@[grind =]
theorem getElem_zero_idxsOf_eq_idxOf_add [BEq α] (h : 0 < ((xs : List α).idxsOf x s).length) :
    (xs.idxsOf x s)[0] = xs.idxOf x + s := getElem_zero_findIdxs_eq_findIdx_add h

@[simp]
theorem getElem_zero_idxsOf_eq_idxOf [BEq α] (h : 0 < ((xs : List α).idxsOf x).length) :
    (xs.idxsOf x)[0] = xs.idxOf x := getElem_zero_idxsOf_eq_idxOf_add h

@[grind =>]
theorem idxOf_add_mem_idxsOf [BEq α] (s : Nat) (h : (xs : List α).idxOf x < xs.length) :
    xs.idxOf x + s ∈ xs.idxsOf x s := findIdx_add_mem_findIdxs s h

theorem idxOf_mem_idxsOf [BEq α] (h : (xs : List α).idxOf x < xs.length) :
    xs.idxOf x ∈ xs.idxsOf x := idxOf_add_mem_idxsOf 0 h

/-! ### idxOfNth -/

@[simp, grind =] theorem idxOfNth_nil [BEq α] : ([] : List α).idxOfNth x n = 0 := rfl

@[grind =]
theorem idxOfNth_cons [BEq α] {a : α} :
    (a :: xs).idxOfNth x n =
    if n = 0 then if a == x then 0 else xs.idxOfNth x 0 + 1
    else if a == x then xs.idxOfNth x (n - 1) + 1
    else xs.idxOfNth x n + 1 := findIdxNth_cons

@[simp] theorem idxOfNth_cons_zero [BEq α] {a : α} :
    (a :: xs).idxOfNth x 0 = if a == x then 0 else xs.idxOfNth x 0 + 1 := by grind

@[simp] theorem idxOfNth_cons_succ [BEq α] {a : α} :
    (a :: xs).idxOfNth x (n + 1) =
    if a == x then xs.idxOfNth x n + 1
    else xs.idxOfNth x (n + 1) + 1 := by grind

theorem idxOfNth_cons_of_not_beq {a : α} [BEq α] (h : (a == x) = false) :
    (a :: xs).idxOfNth x n = xs.idxOfNth x n + 1 := by grind

theorem idxOfNth_cons_of_beq {a : α} [BEq α] (h : a == x) :
    (a :: xs).idxOfNth x n = if n = 0 then 0 else xs.idxOfNth x (n - 1) + 1 := by grind

theorem idxOfNth_cons_zero_of_beq {a : α} [BEq α] (h : a == x) :
    (a :: xs).idxOfNth x 0 = 0 := by grind

theorem idxOfNth_cons_succ_of_beq {a : α} [BEq α] (h : a == x) :
    (a :: xs).idxOfNth x (n + 1) = xs.idxOfNth x n + 1 := by grind

theorem getElem_idxOf_eq_idxOfNth_add {xs : List α} [BEq α] {h : n < (xs.idxsOf x s).length} :
    (xs.idxsOf x s)[n] = xs.idxOfNth x n + s := by
  induction xs generalizing n s <;> grind

@[grind =]
theorem getElem_idxOf_eq_idxOfNth {xs : List α} [BEq α] {h : n < (xs.idxsOf x).length} :
    (xs.idxsOf x)[n] = xs.idxOfNth x n := getElem_idxOf_eq_idxOfNth_add

theorem getElem_idxOfNth_beq {xs : List α} [BEq α] {h : xs.idxOfNth x n < xs.length} :
    xs[xs.idxOfNth x n] == x := pos_findIdxNth_getElem (p := (· == x))

grind_pattern getElem_idxOfNth_beq => xs[xs.idxOfNth x n]

@[simp, grind =]
theorem getElem_idxOfNth_eq {xs : List α} [BEq α] [LawfulBEq α] {h : xs.idxOfNth x n < xs.length} :
    xs[xs.idxOfNth x n] = x := eq_of_beq getElem_idxOfNth_beq

theorem idxOfNth_zero [BEq α] : (xs : List α).idxOfNth x 0 = xs.idxOf x := by
  induction xs <;> grind

@[grind _=_]
theorem idxOfNth_lt_length_iff [BEq α] {xs : List α} :
    xs.idxOfNth x n < xs.length ↔ n < xs.count x := findIdxNth_lt_length_iff

@[grind _=_]
theorem idxOfNth_eq_length_iff [BEq α] {xs : List α} :
    xs.idxOfNth x n = xs.length ↔ xs.count x ≤ n := findIdxNth_eq_length_iff

@[grind .]
theorem idxOfNth_le_length [BEq α] {xs : List α} :
    xs.idxOfNth x n ≤ xs.length := findIdxNth_le_length

theorem idxOfNth_lt_length_of_lt_count {xs : List α} [BEq α] :
    n < xs.count x → xs.idxOfNth x n < xs.length := by grind

theorem idxOfNth_eq_length_of_ge_count {xs : List α} [BEq α] :
    xs.count x ≤ n → xs.idxOfNth x n = xs.length := by grind

theorem idxOfNth_lt_idxOfNth_iff [BEq α] {xs : List α} :
    xs.idxOfNth x n < xs.idxOfNth x m ↔ n < xs.count x ∧ n < m := findIdxNth_lt_findIdxNth_iff

theorem idxOfNth_eq_idxOfNth_iff [BEq α] {xs : List α} :
    xs.idxOfNth x n = xs.idxOfNth x m ↔
    (xs.count x ≤ m ∨ n ≤ m) ∧ (xs.count x ≤ n ∨ m ≤ n) := findIdxNth_eq_findIdxNth_iff

theorem idxOfNth_lt_idxOfNth_iff_of_lt_count [BEq α] {xs : List α} (hn : n < xs.count x) :
    xs.idxOfNth x n < xs.idxOfNth x m ↔ n < m := findIdxNth_lt_findIdxNth_iff_of_lt_countP hn

theorem idxOfNth_mono [BEq α] {xs : List α} (hnm : n ≤ m):
    xs.idxOfNth x n ≤ xs.idxOfNth x m := findIdxNth_mono hnm

theorem idxOfNth_eq_idxOfNth_iff_of_left_lt_count [BEq α] {xs : List α}
    (hn : n < xs.count x) : xs.idxOfNth x n = xs.idxOfNth x m ↔ n = m :=
  findIdxNth_eq_findIdxNth_iff_of_left_lt_countP hn

theorem idxOfNth_eq_idxOfNth_iff_of_right_lt_count [BEq α] {xs : List α}
    (hm : m < xs.count x) : xs.idxOfNth x n = xs.idxOfNth x m ↔ n = m :=
  findIdxNth_eq_findIdxNth_iff_of_right_lt_countP hm

theorem idxOfNth_eq_idxOfNth_of_ge_countP_ge_countP [BEq α] {xs : List α}
    (hn : xs.count x ≤ n) (hm : xs.count x ≤ m) : xs.idxOfNth x n = xs.idxOfNth x m :=
  findIdxNth_eq_findIdxNth_of_ge_countP_ge_countP  hn hm

/-! ### countPBefore -/

@[simp, grind =] theorem countPBefore_nil : ([] : List α).countPBefore p n = 0 := rfl

@[grind =]
theorem countPBefore_cons {a : α} :
    (a :: xs).countPBefore p i =
    if i = 0 then 0 else if p a then xs.countPBefore p (i - 1) + 1
    else xs.countPBefore p (i - 1) := by
  have H : ∀ i s, countPBefore.go (p : α → Bool) xs i s = countPBefore.go p xs i 0 + s := by
    induction xs <;> grind [countPBefore, countPBefore.go, cases Nat]
  cases i <;> grind [countPBefore, countPBefore.go]

theorem countPBefore_cons_zero {a : α} :
    (a :: xs).countPBefore p 0 = 0 := by grind

@[simp] theorem countPBefore_cons_succ {a : α} :
    (a :: xs).countPBefore p (i + 1) =
    if p a then xs.countPBefore p i + 1 else xs.countPBefore p i := by grind

@[simp, grind =] theorem countPBefore_zero :
    (xs : List α).countPBefore p 0 = 0 := by grind [cases List]

@[grind =]
theorem countPBefore_succ :
    (xs : List α).countPBefore p (i + 1) =
    if h : xs = [] then 0
    else if p (xs.head h) then xs.tail.countPBefore p i + 1
    else xs.tail.countPBefore p i := by grind [cases List]

theorem countPBefore_cons_succ_of_neg {a : α} (h : p a = false) :
    (a :: xs).countPBefore p (i + 1) = xs.countPBefore p i := by grind

theorem countPBefore_cons_succ_of_pos {a : α} (h : p a) :
    (a :: xs).countPBefore p (i + 1) = xs.countPBefore p i + 1 := by grind

theorem countPBefore_eq_countP_take : (xs : List α).countPBefore p i = (xs.take i).countP p := by
  induction xs generalizing i <;> grind [cases Nat]

theorem countPBefore_of_ge_length {xs : List α} (hi : xs.length ≤ i) :
    xs.countPBefore p i = xs.countP p := by
  rw [countPBefore_eq_countP_take, take_of_length_le (by grind)]

theorem countPBefore_length {xs : List α} :
    xs.countPBefore p xs.length = xs.countP p := countPBefore_of_ge_length (by grind)

@[simp, grind <=]
theorem findIdxNth_countPBefore_of_lt_length_of_pos {xs : List α} {h : i < xs.length}
    (hip : p xs[i]) : xs.findIdxNth p (xs.countPBefore p i) = i := by
  induction xs generalizing i <;> grind

@[simp, grind <=]
theorem countPBefore_findIdxNth_of_lt_countP {xs : List α} :
    n < xs.countP p → xs.countPBefore p (xs.findIdxNth p n) = n := by
  induction xs generalizing n <;> grind

theorem pos_iff_exists_findIdxNth {xs : List α} {h : i < xs.length} :
    p xs[i] ↔ ∃ n, xs.findIdxNth p n = i := ⟨fun h => ⟨xs.countPBefore p i, by grind⟩, by grind⟩

theorem countPBefore_le_countP {xs : List α} (p : α → Bool) :
    xs.countPBefore p i ≤ xs.countP p := by
  rw [countPBefore_eq_countP_take]
  exact (take_sublist _ _).countP_le

theorem countPBefore_mono {xs : List α} (hij : i ≤ j) :
    xs.countPBefore p i ≤ xs.countPBefore p j := by
  simp only [countPBefore_eq_countP_take]
  exact (take_sublist_take_left hij).countP_le

@[grind <=]
theorem countPBefore_lt_countP_of_lt_length_of_pos {xs : List α} {h : i < xs.length}
    (hip : p xs[i]) : xs.countPBefore p i < xs.countP p := by
  rwa [← findIdxNth_lt_length_iff, findIdxNth_countPBefore_of_lt_length_of_pos hip]

/-! ### countBefore -/

@[simp, grind =] theorem countBefore_nil [BEq α] : ([] : List α).countBefore x i = 0 := rfl

@[grind =]
theorem countBefore_cons [BEq α] {a : α} :
    (a :: xs).countBefore x i =
    if i = 0 then 0 else if a == x then xs.countBefore x (i - 1) + 1
    else xs.countBefore x (i - 1) := countPBefore_cons

@[simp] theorem countBefore_zero [BEq α] : (xs : List α).countBefore p 0 = 0 := countPBefore_zero

@[simp] theorem countBefore_cons_succ {a : α} [BEq α] :
    (a :: xs).countBefore x (i + 1) = xs.countBefore x i + if a == x then 1 else 0 := by grind

theorem countBefore_cons_succ_of_not_beq [BEq α] {a : α} (h : (a == x) = false):
    (a :: xs).countBefore x (i + 1) = xs.countBefore x i := by grind

theorem countBefore_cons_succ_of_beq {a : α} [BEq α] (h : a == x) :
    (a :: xs).countBefore x (i + 1) = xs.countBefore x i + 1 := by grind

theorem countBefore_eq_count_take [BEq α] :
    (xs : List α).countBefore x i = (xs.take i).count x := by
  induction xs generalizing i <;> cases i <;> grind

@[grind <=]
theorem countBefore_idxOfNth_of_lt_count [BEq α] {xs : List α} (hn : n < xs.count x) :
     xs.countBefore x (xs.idxOfNth x n) = n := countPBefore_findIdxNth_of_lt_countP hn

@[grind <=]
theorem idxOfNth_countBefore_of_lt_length_of_beq [BEq α] {xs : List α} {h : i < xs.length}
    (hip : xs[i] == x) : xs.idxOfNth x (xs.countBefore x i) = i :=
  findIdxNth_countPBefore_of_lt_length_of_pos hip

@[simp, grind =]
theorem idxOfNth_countBefore_getElem [BEq α] [ReflBEq α] {xs : List α}
    {h : i < xs.length} : xs.idxOfNth xs[i] (xs.countBefore xs[i] i) = i :=
  idxOfNth_countBefore_of_lt_length_of_beq BEq.rfl

theorem beq_iff_exists_findIdxNth [BEq α] {xs : List α} {h : i < xs.length} :
    xs[i] == x ↔ ∃ n, xs.idxOfNth x n = i := ⟨fun h => ⟨xs.countBefore x i, by grind⟩, by grind⟩

theorem countBefore_le_count [BEq α] {xs : List α} :
    xs.countBefore x i ≤ xs.count x := by
  induction xs generalizing i <;> cases i <;> grind

@[grind <=]
theorem countBefore_lt_count_of_lt_length_of_beq [BEq α] {xs : List α} {h : i < xs.length}
    (hip : xs[i] == x) : xs.countBefore x i < xs.count x :=
  countPBefore_lt_countP_of_lt_length_of_pos hip

@[simp, grind <=]
theorem countBefore_lt_count_getElem [BEq α] [ReflBEq α] {xs : List α} {h : i < xs.length} :
    xs.countBefore xs[i] i < xs.count xs[i] :=
  countBefore_lt_count_of_lt_length_of_beq BEq.rfl

theorem countBefore_of_ge_length [BEq α] {xs : List α} (hi : xs.length ≤ i) :
    xs.countBefore x i = xs.count x := countPBefore_of_ge_length hi

/-! ### insertP -/

theorem insertP_loop (a : α) (l r : List α) :
    insertP.loop p a l r = reverseAux r (insertP p a l) := by
  induction l generalizing r with simp [insertP, insertP.loop, cond]
  | cons b l ih => rw [ih (b :: r), ih [b]]; split <;> simp

@[simp] theorem insertP_nil (p : α → Bool) (a) : insertP p a [] = [a] := rfl

@[simp] theorem insertP_cons_pos (p : α → Bool) (a b l) (h : p b) :
    insertP p a (b :: l) = a :: b :: l := by
  simp only [insertP, insertP.loop, cond, h]; rfl

@[simp] theorem insertP_cons_neg (p : α → Bool) (a b l) (h : ¬ p b) :
    insertP p a (b :: l) = b :: insertP p a l := by
  simp only [insertP, insertP.loop, cond, h]; exact insertP_loop ..

@[simp] theorem length_insertP (p : α → Bool) (a l) : (insertP p a l).length = l.length + 1 := by
  induction l with simp [insertP, insertP.loop, cond]
  | cons _ _ ih => split <;> simp [insertP_loop, ih]

@[simp] theorem mem_insertP (p : α → Bool) (a l) : a ∈ insertP p a l := by
  induction l with simp [insertP, insertP.loop, cond]
  | cons _ _ ih => split <;> simp [insertP_loop, ih]

/-! ### dropPrefix?, dropSuffix?, dropInfix?-/

open Option

@[simp] theorem dropPrefix?_nil [BEq α] {p : List α} : dropPrefix? p [] = some p := by
  simp [dropPrefix?]

theorem dropPrefix?_eq_some_iff [BEq α] {l p s : List α} :
    dropPrefix? l p = some s ↔ ∃ p', l = p' ++ s ∧ p' == p := by
  unfold dropPrefix?
  split
  · simp
  · simp
  · rename_i a as b bs
    simp only [ite_none_right_eq_some]
    constructor
    · rw [dropPrefix?_eq_some_iff]
      rintro ⟨w, p', rfl, h⟩
      refine ⟨a :: p', by simp_all⟩
    · rw [dropPrefix?_eq_some_iff]
      rintro ⟨p, h, w⟩
      rw [cons_eq_append_iff] at h
      obtain (⟨rfl, rfl⟩ | ⟨a', rfl, rfl⟩) := h
      · simp at w
      · simp only [cons_beq_cons, Bool.and_eq_true] at w
        refine ⟨w.1, a', rfl, w.2⟩

theorem dropPrefix?_append_of_beq [BEq α] {l₁ l₂ : List α} (p : List α) (h : l₁ == l₂) :
    dropPrefix? (l₁ ++ p) l₂ = some p := by
  simp [dropPrefix?_eq_some_iff, h]

theorem dropSuffix?_eq_some_iff [BEq α] {l p s : List α} :
    dropSuffix? l s = some p ↔ ∃ s', l = p ++ s' ∧ s' == s := by
  unfold dropSuffix?
  rw [splitAt_eq]
  simp only [ite_none_right_eq_some, some.injEq]
  constructor
  · rintro ⟨w, rfl⟩
    refine ⟨_, by simp, w⟩
  · rintro ⟨s', rfl, w⟩
    simp [length_eq_of_beq w, w]

@[simp] theorem dropSuffix?_nil [BEq α] {s : List α} : dropSuffix? s [] = some s := by
  simp [dropSuffix?_eq_some_iff]

theorem dropInfix?_go_eq_some_iff [BEq α] {i l acc p s : List α} :
    dropInfix?.go i l acc = some (p, s) ↔ ∃ p',
      p = acc.reverse ++ p' ∧
      -- `i` is an infix up to `==`
      (∃ i', l = p' ++ i' ++ s ∧ i' == i) ∧
        -- and there is no shorter prefix for which that is the case
        (∀ p'' i'' s'', l = p'' ++ i'' ++ s'' → i'' == i → p''.length ≥ p'.length) := by
  unfold dropInfix?.go
  split
  · simp only [isEmpty_iff, ite_none_right_eq_some, some.injEq, Prod.mk.injEq, nil_eq,
      append_assoc, append_eq_nil_iff, ge_iff_le, and_imp]
    constructor
    · rintro ⟨rfl, rfl, rfl⟩
      simp
    · rintro ⟨p', rfl, ⟨_, ⟨rfl, rfl, rfl⟩, h⟩, w⟩
      simp_all
  · rename_i a t
    split <;> rename_i h
    · rw [dropInfix?_go_eq_some_iff]
      constructor
      · rintro ⟨p', rfl, ⟨i', rfl, h₂⟩, w⟩
        refine ⟨a :: p', ?_⟩
        simp [h₂]
        intro p'' i'' s'' h₁ h₂
        rw [cons_eq_append_iff] at h₁
        obtain (⟨rfl, h₁⟩ | ⟨p'', rfl, h₁⟩) := h₁
        · rw [append_assoc, ← h₁] at h
          have := dropPrefix?_append_of_beq s'' h₂
          simp_all
        · simpa using w p'' i'' s'' (by simpa using h₁) h₂
      · rintro ⟨p', rfl, ⟨i', h₁, h₂⟩, w⟩
        rw [cons_eq_append_iff] at h₁
        simp at h₁
        obtain (⟨⟨rfl, rfl⟩, rfl⟩ | ⟨a', h₁, rfl⟩) := h₁
        · simp only [nil_beq_eq, isEmpty_iff] at h₂
          simp only [h₂] at h
          simp at h
        · rw [append_eq_cons_iff] at h₁
          obtain (⟨rfl, rfl⟩ | ⟨p', rfl, rfl⟩) := h₁
          · rw [← cons_append] at h
            have := dropPrefix?_append_of_beq s h₂
            simp_all
          · refine ⟨p', ?_⟩
            simp only [reverse_cons, append_assoc, singleton_append, append_cancel_left_eq,
              append_cancel_right_eq, exists_eq_left', ge_iff_le, true_and]
            refine ⟨h₂, ?_⟩
            intro p'' i'' s'' h₃ h₄
            rw [← append_assoc] at h₃
            rw [h₃] at w
            simpa using w (a :: p'') i'' s'' (by simp) h₄
    · rename_i s'
      simp only [some.injEq, Prod.mk.injEq, append_assoc, ge_iff_le]
      rw [dropPrefix?_eq_some_iff] at h
      obtain ⟨p', h, w⟩ := h
      constructor
      · rintro ⟨rfl, rfl⟩
        simpa using ⟨p', by simp_all⟩
      · rintro ⟨p'', rfl, ⟨i', h₁, h₂⟩, w'⟩
        specialize w' [] p' s' (by simpa using h) w
        simp at w'
        simp [w'] at h₁ ⊢
        rw [h] at h₁
        apply append_inj_right h₁
        replace w := length_eq_of_beq w
        replace h₂ := length_eq_of_beq h₂
        simp_all

theorem dropInfix?_eq_some_iff [BEq α] {l i p s : List α} :
    dropInfix? l i = some (p, s) ↔
      -- `i` is an infix up to `==`
      (∃ i', l = p ++ i' ++ s ∧ i' == i) ∧
        -- and there is no shorter prefix for which that is the case
        (∀ p' i' s', l = p' ++ i' ++ s' → i' == i → p'.length ≥ p.length) := by
  unfold dropInfix?
  rw [dropInfix?_go_eq_some_iff]
  simp

@[simp] theorem dropInfix?_nil [BEq α] {s : List α} : dropInfix? s [] = some ([], s) := by
  simp [dropInfix?_eq_some_iff]

/-! ### IsPrefixOf?, IsSuffixOf? -/

@[simp] theorem isSome_isPrefixOf?_eq_isPrefixOf [BEq α] (xs ys : List α) :
    (xs.isPrefixOf? ys).isSome = xs.isPrefixOf ys := by
  match xs, ys with
  | [], _ => simp [List.isPrefixOf?]
  | _::_, [] => rfl
  | _::_, _::_ =>
    simp only [List.isPrefixOf?, List.isPrefixOf]
    split <;> simp [*, isSome_isPrefixOf?_eq_isPrefixOf]

@[simp] theorem isPrefixOf?_eq_some_iff_append_eq [BEq α] [LawfulBEq α] {xs ys zs : List α} :
    xs.isPrefixOf? ys = some zs ↔ xs ++ zs = ys := by
  induction xs generalizing ys with
  | nil => simp [isPrefixOf?, Eq.comm]
  | cons => cases ys <;> simp [isPrefixOf?, *]

theorem append_eq_of_isPrefixOf?_eq_some [BEq α] [LawfulBEq α] {xs ys zs : List α}
    (h : xs.isPrefixOf? ys = some zs) : xs ++ zs = ys := by simp_all

@[simp] theorem isSome_isSuffixOf?_eq_isSuffixOf [BEq α] (xs ys : List α) :
    (xs.isSuffixOf? ys).isSome = xs.isSuffixOf ys := by
  simp [List.isSuffixOf?, isSuffixOf]

@[simp] theorem isSuffixOf?_eq_some_iff_append_eq [BEq α] [LawfulBEq α] {xs ys zs : List α} :
    xs.isSuffixOf? ys = some zs ↔ zs ++ xs = ys := by
  simp only [isSuffixOf?, map_eq_some_iff, isPrefixOf?_eq_some_iff_append_eq]
  constructor
  · intro
    | ⟨_, h, heq⟩ =>
      rw [List.reverse_eq_iff] at heq
      rw [heq] at h
      rw [← reverse_inj, reverse_append, h]
  · intro h
    exists zs.reverse
    simp [← h]

theorem append_eq_of_isSuffixOf?_eq_some [BEq α] [LawfulBEq α] {xs ys zs : List α}
    (h : xs.isSuffixOf? ys = some zs) : zs ++ xs = ys := by simp_all

/-! ### finRange -/

theorem get_finRange (i : Fin (finRange n).length) :
    (finRange n).get i = Fin.cast length_finRange i := by simp

@[simp, grind =]
theorem finRange_eq_nil_iff : finRange n = [] ↔ n = 0 := by
  simp [eq_nil_iff_length_eq_zero]

theorem finRange_eq_pmap_range : finRange n = (range n).pmap Fin.mk (by simp) := by
  apply List.ext_getElem <;> simp [finRange]

theorem nodup_finRange (n) : (finRange n).Nodup := by
  rw [finRange_eq_pmap_range]
  exact (Pairwise.pmap nodup_range _) fun _ _ _ _ => @Fin.ne_of_val_ne _ ⟨_, _⟩ ⟨_, _⟩

theorem pairwise_lt_finRange (n) : Pairwise (· < ·) (finRange n) := by
  rw [finRange_eq_pmap_range]
  exact List.pairwise_lt_range.pmap (by simp) (by simp)

theorem pairwise_le_finRange (n) : Pairwise (· ≤ ·) (finRange n) := by
  rw [finRange_eq_pmap_range]
  exact List.pairwise_le_range.pmap (by simp) (by simp)

@[simp]
theorem map_get_finRange (l : List α) : (finRange l.length).map l.get = l := by
  apply ext_getElem <;> simp

@[simp]
theorem map_getElem_finRange (l : List α) : (finRange l.length).map (l[·.1]) = l := by
  apply ext_getElem <;> simp

@[simp]
theorem map_coe_finRange_eq_range : (finRange n).map (↑·) = List.range n := by
  apply List.ext_getElem <;> simp
/-! ### sum/prod -/

private theorem foldr_eq_foldl_aux (f : α → α → α) (init : α) [Std.Associative f]
    [Std.LawfulIdentity f init] {l : List α} :
    l.foldl f a = f a (l.foldl f init) := by
  induction l generalizing a with
  | nil => simp [Std.LawfulRightIdentity.right_id]
  | cons b l ih =>
    simp [Std.LawfulLeftIdentity.left_id, ih (a := f a b), ih (a := b), Std.Associative.assoc]

theorem foldr_eq_foldl (f : α → α → α) (init : α) [Std.Associative f]
    [Std.LawfulIdentity f init] {l : List α} :
    l.foldr f init = l.foldl f init := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih, Std.LawfulLeftIdentity.left_id, foldr_eq_foldl_aux (a := a)]

@[simp, grind =]
theorem prod_nil [Mul α] [One α] : ([] : List α).prod = 1 := rfl

@[simp, grind =]
theorem prod_cons [Mul α] [One α] {a : α} {l : List α} : (a :: l).prod = a * l.prod := rfl

theorem prod_one_cons [Mul α] [One α] [Std.LawfulLeftIdentity (α := α) (· * ·) 1] {l : List α} :
    (1 :: l).prod = l.prod := by simp [Std.LawfulLeftIdentity.left_id]

theorem prod_singleton [Mul α] [One α] [Std.LawfulRightIdentity (α := α) (· * ·) 1] {a : α} :
  [a].prod = a := by simp [Std.LawfulRightIdentity.right_id]

theorem prod_pair [Mul α] [One α] [Std.LawfulRightIdentity (α := α) (· * ·) 1] {a b : α} :
  [a, b].prod = a * b := by simp [Std.LawfulRightIdentity.right_id]

@[simp, grind =]
theorem prod_append [Mul α] [One α] [Std.LawfulLeftIdentity (α := α) (· * ·) 1]
    [Std.Associative (α := α) (· * ·)] {l₁ l₂ : List α} : (l₁ ++ l₂).prod = l₁.prod * l₂.prod := by
  induction l₁ with simp [Std.LawfulLeftIdentity.left_id, Std.Associative.assoc, *]

theorem prod_concat [Mul α] [One α] [Std.LawfulIdentity (α := α) (· * ·) 1]
    [Std.Associative (α := α) (· * ·)] {l : List α} {a : α} :
    (l.concat a).prod = l.prod * a := by simp [Std.LawfulRightIdentity.right_id]

@[simp, grind =]
theorem prod_flatten [Mul α] [One α] [Std.LawfulIdentity (α := α) (· * ·) 1]
    [Std.Associative (α := α) (· * ·)] {l : List (List α)} :
    l.flatten.prod = (l.map prod).prod := by
  induction l with simp [*]

theorem prod_eq_foldr [Mul α] [One α] {l : List α} :
    l.prod = l.foldr (· * ·) 1 := rfl

theorem prod_eq_foldl [Mul α] [One α] [Std.Associative (α := α) (· * ·)]
    [Std.LawfulIdentity (α := α) (· * ·) 1] {l : List α} :
    l.prod = l.foldl (· * ·) 1 := foldr_eq_foldl ..

theorem sum_zero_cons [Add α] [Zero α] [Std.LawfulLeftIdentity (α := α) (· + ·) 0] {l : List α} :
    (0 :: l).sum = l.sum := by simp [Std.LawfulLeftIdentity.left_id]

theorem sum_singleton [Add α] [Zero α] [Std.LawfulRightIdentity (α := α) (· + ·) 0] {a : α} :
  [a].sum = a := by simp [Std.LawfulRightIdentity.right_id]

theorem sum_pair [Add α] [Zero α] [Std.LawfulRightIdentity (α := α) (· + ·) 0] {a b : α} :
  [a, b].sum = a + b := by simp [Std.LawfulRightIdentity.right_id]

@[simp, grind =]
theorem sum_append [Add α] [Zero α] [Std.LawfulLeftIdentity (α := α) (· + ·) 0]
    [Std.Associative (α := α) (· + ·)] {l₁ l₂ : List α} : (l₁ ++ l₂).sum = l₁.sum + l₂.sum := by
  induction l₁ with simp [Std.LawfulLeftIdentity.left_id, Std.Associative.assoc, *]

theorem sum_concat [Add α] [Zero α] [Std.LawfulIdentity (α := α) (· + ·) 0]
    [Std.Associative (α := α) (· + ·)] {l : List α} {a : α} :
    (l.concat a).sum = l.sum + a := by simp [Std.LawfulRightIdentity.right_id]

@[simp, grind =]
theorem sum_flatten [Add α] [Zero α] [Std.LawfulIdentity (α := α) (· + ·) 0]
    [Std.Associative (α := α) (· + ·)] {l : List (List α)} :
    l.flatten.sum = (l.map sum).sum := by
  induction l with simp [*]

theorem sum_eq_foldr [Add α] [Zero α] {l : List α} :
    l.sum = l.foldr (· + ·) 0 := rfl

theorem sum_eq_foldl [Add α] [Zero α] [Std.Associative (α := α) (· + ·)]
    [Std.LawfulIdentity (α := α) (· + ·) 0] {l : List α} :
    l.sum = l.foldl (· + ·) 0 := foldr_eq_foldl ..

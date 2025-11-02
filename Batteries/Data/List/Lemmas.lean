/-
Copyright (c) 2014 Parikshit Khanna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Parikshit Khanna, Jeremy Avigad, Leonardo de Moura, Floris van Doorn, Mario Carneiro
-/
module

public import Batteries.Control.ForInStep.Lemmas
public import Batteries.Data.List.Basic
public import Batteries.Tactic.Alias

@[expose] public section

namespace List

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

theorem findIdx_eq_findIdx? (p : α → Bool) (l : List α) :
    l.findIdx p = (match l.findIdx? p with | some i => i | none => l.length) := by grind

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

@[deprecated (since := "2025-09-19")]
alias rel_of_chain_cons := rel_of_isChain_cons_cons

theorem isChain_cons_of_isChain_cons_cons (p : IsChain R (a :: b :: l)) :
    IsChain R (b :: l) := (isChain_cons_cons.1 p).2

@[deprecated (since := "2025-09-19")]
alias chain_of_chain_cons := isChain_cons_of_isChain_cons_cons

theorem isChain_of_isChain_cons (p : IsChain R (b :: l)) :
    IsChain R l := by
  cases l
  · exact .nil
  · exact isChain_cons_of_isChain_cons_cons p

theorem isChain_of_isChain_cons_cons (p : IsChain R (a :: b :: l)) :
    IsChain R l := isChain_of_isChain_cons (isChain_of_isChain_cons p)

theorem IsChain.imp (H : ∀ ⦃a b : α⦄, R a b → S a b)
    (p : IsChain R l) : IsChain S l := by induction p with grind

@[deprecated (since := "2025-09-19")]
alias Chain.imp := IsChain.imp

theorem IsChain.cons_of_imp_of_cons (h : ∀ c, R a c → R b c) :
    IsChain R (a :: l) → IsChain R (b :: l) := by cases l <;> grind

@[deprecated "Use IsChain.imp and IsChain.change_head" (since := "2025-09-19")]
theorem Chain.imp' (HRS : ∀ ⦃a b : α⦄, R a b → S a b)
    (Hab : ∀ ⦃c⦄, R a c → S b c) : IsChain R (a :: l) → IsChain S (b :: l) := by
  cases l with grind [IsChain.imp]

@[deprecated (since := "2025-09-19")]
protected alias Pairwise.chain := Pairwise.isChain

@[grind →] protected theorem IsChain.pairwise [Trans R R R] (c : IsChain R l) :
    Pairwise R l := by
  induction c with
  | nil | singleton => grind
  | cons_cons hr h p =>
    simp only [pairwise_cons, mem_cons, forall_eq_or_imp] at p ⊢
    exact ⟨⟨hr, fun _ ha => Trans.trans hr <| p.1 _ ha⟩, p⟩

theorem isChain_iff_pairwise [Trans R R R] : IsChain R l ↔ Pairwise R l := by grind

theorem isChain_iff_getElem {l : List α} :
    IsChain R l ↔ ∀ (i : Nat) (_hi : i + 1 < l.length), R l[i] l[i + 1] := by
  induction l with
  | nil => grind
  | cons a l IH => cases l with | nil => grind | cons b l => simp [IH, Nat.forall_lt_succ_left']

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

/-! ### indexOf and indexesOf -/

theorem foldrIdx_start :
    (xs : List α).foldrIdx f i s = (xs : List α).foldrIdx (fun i => f (i + s)) i := by
  induction xs generalizing f i s with grind [foldrIdx]

@[simp] theorem foldrIdx_cons :
    (x :: xs : List α).foldrIdx f i s = f s x (foldrIdx f i xs (s + 1)) := rfl

theorem findIdxs_cons_aux (p : α → Bool) :
    foldrIdx (fun i a is => if p a = true then (i + 1) :: is else is) [] xs s =
      map (· + 1) (foldrIdx (fun i a is => if p a = true then i :: is else is) [] xs s) := by
  induction xs generalizing s with grind [foldrIdx]

theorem findIdxs_cons :
    (x :: xs : List α).findIdxs p =
      bif p x then 0 :: (xs.findIdxs p).map (· + 1) else (xs.findIdxs p).map (· + 1) := by
  dsimp [findIdxs]
  rw [cond_eq_if]
  split <;>
  · simp only [foldrIdx_start, Nat.add_zero, cons.injEq, true_and]
    apply findIdxs_cons_aux

@[simp, grind =] theorem indexesOf_nil [BEq α] : ([] : List α).indexesOf x = [] := rfl

@[grind =]
theorem indexesOf_cons [BEq α] : (x :: xs : List α).indexesOf y =
    bif x == y then 0 :: (xs.indexesOf y).map (· + 1) else (xs.indexesOf y).map (· + 1) := by
  simp [indexesOf, findIdxs_cons]

@[simp] theorem eraseIdx_idxOf_eq_erase [BEq α] (a : α) (l : List α) :
    l.eraseIdx (l.idxOf a) = l.erase a := by
  induction l with grind

theorem idxOf_mem_indexesOf [BEq α] [LawfulBEq α] {xs : List α} (m : x ∈ xs) :
    xs.idxOf x ∈ xs.indexesOf x := by
  induction xs with grind

theorem idxOf_eq_idxOf? [BEq α] (a : α) (l : List α) :
    l.idxOf a = (match l.idxOf? a with | some i => i | none => l.length) := by
  simp [idxOf, idxOf?, findIdx_eq_findIdx?]

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

/-! ### sum/prod -/

theorem prod_eq_foldr [Mul α] [One α] {l : List α} :
    l.prod = l.foldr (· * ·) 1 := rfl

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

theorem prod_append [Mul α] [One α] [Std.LawfulLeftIdentity (α := α) (· * ·) 1]
    [Std.Associative (α := α) (· * ·)] {l₁ l₂ : List α} : (l₁ ++ l₂).prod = l₁.prod * l₂.prod := by
  induction l₁ with simp [Std.LawfulLeftIdentity.left_id, Std.Associative.assoc, *]

theorem prod_concat [Mul α] [One α] [Std.LawfulIdentity (α := α) (· * ·) 1]
    [Std.Associative (α := α) (· * ·)] {l : List α} {a : α} :
    (l.concat a).prod = l.prod * a := by simp [prod_append, Std.LawfulRightIdentity.right_id]

theorem prod_flatten [Mul α] [One α] [Std.LawfulIdentity (α := α) (· * ·) 1]
    [Std.Associative (α := α) (· * ·)] {l : List (List α)} :
    l.flatten.prod = (l.map prod).prod := by
  induction l with simp [prod_append, *]

theorem sum_eq_foldr [Add α] [Zero α] {l : List α} :
    l.sum = l.foldr (· + ·) 0 := rfl

theorem sum_zero_cons [Add α] [Zero α] [Std.LawfulLeftIdentity (α := α) (· + ·) 0] {l : List α} :
    (0 :: l).sum = l.sum := by simp [Std.LawfulLeftIdentity.left_id]

theorem sum_singleton [Add α] [Zero α] [Std.LawfulRightIdentity (α := α) (· + ·) 0] {a : α} :
  [a].sum = a := by simp [Std.LawfulRightIdentity.right_id]

theorem sum_pair [Add α] [Zero α] [Std.LawfulRightIdentity (α := α) (· + ·) 0] {a b : α} :
  [a, b].sum = a + b := by simp [Std.LawfulRightIdentity.right_id]

theorem sum_append [Add α] [Zero α] [Std.LawfulLeftIdentity (α := α) (· + ·) 0]
    [Std.Associative (α := α) (· + ·)] {l₁ l₂ : List α} : (l₁ ++ l₂).sum = l₁.sum + l₂.sum := by
  induction l₁ with simp [Std.LawfulLeftIdentity.left_id, Std.Associative.assoc, *]

theorem sum_concat [Add α] [Zero α] [Std.LawfulIdentity (α := α) (· + ·) 0]
    [Std.Associative (α := α) (· + ·)] {l : List α} {a : α} :
    (l.concat a).sum = l.sum + a := by simp [sum_append, Std.LawfulRightIdentity.right_id]

theorem sum_flatten [Add α] [Zero α] [Std.LawfulIdentity (α := α) (· + ·) 0]
    [Std.Associative (α := α) (· + ·)] {l : List (List α)} :
    l.flatten.sum = (l.map sum).sum := by
  induction l with simp [sum_append, *]

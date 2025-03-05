/-
Copyright (c) 2014 Parikshit Khanna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Parikshit Khanna, Jeremy Avigad, Leonardo de Moura, Floris van Doorn, Mario Carneiro
-/
import Batteries.Control.ForInStep.Lemmas
import Batteries.Data.List.Basic
import Batteries.Tactic.Init
import Batteries.Tactic.Alias

namespace List

/-! ### toArray-/

@[simp] theorem getElem_mk {xs : List α} {i : Nat} (h : i < xs.length) :
    (Array.mk xs)[i] = xs[i] := rfl

/-! ### next? -/

@[simp] theorem next?_nil : @next? α [] = none := rfl
@[simp] theorem next?_cons (a l) : @next? α (a :: l) = some (a, l) := rfl

/-! ### dropLast -/

theorem dropLast_eq_eraseIdx {xs : List α} {i : Nat} (last_idx : i + 1 = xs.length) :
    xs.dropLast = List.eraseIdx xs i := by
  induction i generalizing xs with
  | zero =>
    let [x] := xs
    rfl
  | succ n ih =>
    let x::xs := xs
    simp at last_idx
    rw [dropLast, eraseIdx]
    congr
    exact ih last_idx
    exact fun _ => nomatch xs

/-! ### set -/

theorem set_eq_modify (a : α) : ∀ n (l : List α), set l n a = modify (fun _ => a) n l
  | 0, l => by cases l <;> rfl
  | _+1, [] => rfl
  | _+1, _ :: _ => congrArg (cons _) (set_eq_modify _ _ _)

theorem set_eq_take_cons_drop (a : α) {n l} (h : n < length l) :
    set l n a = take n l ++ a :: drop (n + 1) l := by
  rw [set_eq_modify, modify_eq_take_cons_drop h]

theorem modify_eq_set_getElem? (f : α → α) :
    ∀ n (l : List α), l.modify f n = ((fun a => l.set n (f a)) <$> l[n]?).getD l
  | 0, l => by cases l <;> simp
  | _+1, [] => rfl
  | n+1, b :: l =>
    (congrArg (cons _) (modify_eq_set_getElem? ..)).trans <| by cases h : l[n]? <;> simp [h]

@[deprecated (since := "2025-02-15")] alias modify_eq_set_get? := modify_eq_set_getElem?

theorem modify_eq_set_get (f : α → α) {n} {l : List α} (h) :
    l.modify f n = l.set n (f (l.get ⟨n, h⟩)) := by
  rw [modify_eq_set_getElem?, getElem?_eq_getElem h]; rfl

theorem getElem?_set_eq_of_lt (a : α) {n} {l : List α} (h : n < length l) :
    (set l n a)[n]? = some a := by rw [getElem?_set_self', getElem?_eq_getElem h]; rfl

theorem getElem?_set_of_lt (a : α) {m n} (l : List α) (h : n < length l) :
    (set l m a)[n]? = if m = n then some a else l[n]? := by
  simp [getElem?_set', getElem?_eq_getElem h]

@[deprecated (since := "2025-02-15")] alias get?_set_of_lt := getElem?_set_of_lt

theorem getElem?_set_of_lt' (a : α) {m n} (l : List α) (h : m < length l) :
    (set l m a)[n]? = if m = n then some a else l[n]? := by
  simp [getElem?_set]; split <;> subst_vars <;> simp [*, getElem?_eq_getElem h]

@[deprecated (since := "2025-02-15")] alias get?_set_of_lt' := getElem?_set_of_lt'

/-! ### tail -/

theorem length_tail_add_one (l : List α) (h : 0 < length l) : (length (tail l)) + 1 = length l := by
  simp [Nat.sub_add_cancel h]

/-! ### eraseP -/

@[simp] theorem extractP_eq_find?_eraseP
    (l : List α) : extractP p l = (find? p l, eraseP p l) := by
  let rec go (acc) : ∀ xs, l = acc.toList ++ xs →
    extractP.go p l xs acc = (xs.find? p, acc.toList ++ xs.eraseP p)
  | [] => fun h => by simp [extractP.go, find?, eraseP, h]
  | x::xs => by
    simp [extractP.go, find?, eraseP]; cases p x <;> simp
    · intro h; rw [go _ xs]; {simp}; simp [h]
  exact go #[] _ rfl

/-! ### erase -/

theorem erase_eq_self_iff_forall_bne [BEq α] (a : α) (xs : List α) :
    xs.erase a = xs ↔ ∀ (x : α), x ∈ xs → ¬x == a := by
  rw [erase_eq_eraseP', eraseP_eq_self_iff]

/-! ### findIdx? -/

theorem findIdx_eq_findIdx? (p : α → Bool) (l : List α) :
    l.findIdx p = (match l.findIdx? p with | some i => i | none => l.length) := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    rw [findIdx_cons, findIdx?_cons]
    if h : p x then
      simp [h]
    else
      cases h' : findIdx? p xs <;> simp [h, h', ih]

/-! ### replaceF -/

theorem replaceF_nil : [].replaceF p = [] := rfl

theorem replaceF_cons (a : α) (l : List α) :
    (a :: l).replaceF p = match p a with
      | none => a :: replaceF p l
      | some a' => a' :: l := rfl

theorem replaceF_cons_of_some {l : List α} (p) (h : p a = some a') :
    (a :: l).replaceF p = a' :: l := by
  simp [replaceF_cons, h]

theorem replaceF_cons_of_none {l : List α} (p) (h : p a = none) :
    (a :: l).replaceF p = a :: l.replaceF p := by simp [replaceF_cons, h]

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

@[simp] theorem disjoint_nil_left (l : List α) : Disjoint [] l := fun a => (not_mem_nil a).elim

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

@[simp] theorem nil_union (l : List α) : nil ∪ l = l := by simp [List.union_def, foldr]

@[simp] theorem cons_union (a : α) (l₁ l₂ : List α) :
    (a :: l₁) ∪ l₂ = (l₁ ∪ l₂).insert a := by simp [List.union_def, foldr]

@[simp] theorem mem_union_iff [LawfulBEq α] {x : α} {l₁ l₂ : List α} :
    x ∈ l₁ ∪ l₂ ↔ x ∈ l₁ ∨ x ∈ l₂ := by induction l₁ <;> simp [*, or_assoc]

end union

/-! ### inter -/

theorem inter_def [BEq α] (l₁ l₂ : List α)  : l₁ ∩ l₂ = filter (elem · l₂) l₁ := rfl

@[simp] theorem mem_inter_iff [BEq α] [LawfulBEq α] {x : α} {l₁ l₂ : List α} :
    x ∈ l₁ ∩ l₂ ↔ x ∈ l₁ ∧ x ∈ l₂ := by
  cases l₁ <;> simp [List.inter_def, mem_filter]

/-! ### product -/

/-- List.prod satisfies a specification of cartesian product on lists. -/
@[simp]
theorem pair_mem_product {xs : List α} {ys : List β} {x : α} {y : β} :
    (x, y) ∈ product xs ys ↔ x ∈ xs ∧ y ∈ ys := by
  simp only [product, and_imp, mem_map, Prod.mk.injEq,
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
  | [], _, _ => erase_sublist _ _
  | b :: l₁, l₂, h => by
    if heq : b = a then
      simp [heq]
    else
      simp [heq, erase_comm a]
      exact (erase_cons_head b _ ▸ h.erase b).erase_diff_erase_sublist

end Diff

/-! ### prefix, suffix, infix -/

section

variable [DecidableEq α]

theorem commonPrefix_comm (l₁ l₂ : List α) : commonPrefix l₁ l₂ = commonPrefix l₂ l₁ := by
  cases l₁ <;> cases l₂ <;> simp only [commonPrefix]
  next a₁ l₁ a₂ l₂ =>
  split
  · subst a₁
    simp only [↓reduceIte, cons.injEq, true_and]
    apply commonPrefix_comm
  · next h =>
    simp [Ne.symm h]

theorem commonPrefix_prefix_left (l₁ l₂ : List α) : commonPrefix l₁ l₂ <+: l₁ := by
  match l₁, l₂ with
  | [],   _  => simp [commonPrefix]
  | _::_, [] => simp [commonPrefix]
  | a₁::l₁, a₂::l₂ =>
    simp only [commonPrefix]
    split
    · next h =>
      simp only [h, ↓reduceIte, cons_prefix_cons, true_and]
      apply commonPrefix_prefix_left
    · next h =>
      simp [h]

theorem commonPrefix_prefix_right (l₁ l₂ : List α) : commonPrefix l₁ l₂ <+: l₂ := by
  rw [commonPrefix_comm]
  apply commonPrefix_prefix_left

theorem commonPrefix_append_append (p l₁ l₂ : List α) :
    commonPrefix (p ++ l₁) (p ++ l₂) = p ++ commonPrefix l₁ l₂ := by
  match p with
  | []   => rfl
  | a::p => simpa [commonPrefix] using commonPrefix_append_append p l₁ l₂

theorem not_prefix_and_not_prefix_symm_iff {l₁ l₂ : List α} (hp : commonPrefix l₁ l₂ = []) :
    ¬l₁ <+: l₂ ∧ ¬l₂ <+: l₁ ↔ l₁ ≠ [] ∧ l₂ ≠ [] ∧ l₁.head? ≠ l₂.head? := by
  match l₁, l₂ with
  | [], _  => simp
  | _,  [] => simp
  | a₁::l₁, a₂::l₂ =>
    simp only [commonPrefix, ite_eq_right_iff, reduceCtorEq, imp_false] at hp
    simp [hp, Ne.symm hp]

end

/-! ### drop -/

theorem disjoint_take_drop : ∀ {l : List α}, l.Nodup → m ≤ n → Disjoint (l.take m) (l.drop n)
  | [], _, _ => by simp
  | x :: xs, hl, h => by
    cases m <;> cases n <;> simp only [disjoint_cons_left, drop, not_mem_nil, disjoint_nil_left,
      take, not_false_eq_true, and_self]
    · case succ.zero => cases h
    · cases hl with | cons h₀ h₁ =>
      refine ⟨fun h => h₀ _ (mem_of_mem_drop h) rfl, ?_⟩
      exact disjoint_take_drop h₁ (Nat.le_of_succ_le_succ h)

/-! ### Chain -/

attribute [simp] Chain.nil

@[simp]
theorem chain_cons {a b : α} {l : List α} : Chain R a (b :: l) ↔ R a b ∧ Chain R b l :=
  ⟨fun p => by cases p with | cons n p => exact ⟨n, p⟩,
   fun ⟨n, p⟩ => p.cons n⟩

theorem rel_of_chain_cons {a b : α} {l : List α} (p : Chain R a (b :: l)) : R a b :=
  (chain_cons.1 p).1

theorem chain_of_chain_cons {a b : α} {l : List α} (p : Chain R a (b :: l)) : Chain R b l :=
  (chain_cons.1 p).2

theorem Chain.imp' {R S : α → α → Prop} (HRS : ∀ ⦃a b⦄, R a b → S a b) {a b : α}
    (Hab : ∀ ⦃c⦄, R a c → S b c) {l : List α} (p : Chain R a l) : Chain S b l := by
  induction p generalizing b with
  | nil => constructor
  | cons r _ ih =>
    constructor
    · exact Hab r
    · exact ih (@HRS _)

theorem Chain.imp {R S : α → α → Prop} (H : ∀ a b, R a b → S a b) {a : α} {l : List α}
    (p : Chain R a l) : Chain S a l :=
  p.imp' H (H a)

protected theorem Pairwise.chain (p : Pairwise R (a :: l)) : Chain R a l := by
  let ⟨r, p'⟩ := pairwise_cons.1 p; clear p
  induction p' generalizing a with
  | nil => exact Chain.nil
  | @cons b l r' _ IH =>
    simp only [chain_cons, forall_mem_cons] at r
    exact chain_cons.2 ⟨r.1, IH r'⟩

/-! ### range', range -/

theorem chain_succ_range' : ∀ s n step : Nat,
    Chain (fun a b => b = a + step) s (range' (s + step) n step)
  | _, 0, _ => Chain.nil
  | s, n + 1, step => (chain_succ_range' (s + step) n step).cons rfl

theorem chain_lt_range' (s n : Nat) {step} (h : 0 < step) :
    Chain (· < ·) s (range' (s + step) n step) :=
  (chain_succ_range' s n step).imp fun _ _ e => e.symm ▸ Nat.lt_add_of_pos_right h

set_option linter.deprecated false in
@[deprecated getElem?_range' (since := "2024-06-12")]
theorem get?_range' (s step) {m n : Nat} (h : m < n) :
    get? (range' s n step) m = some (s + step * m) := by
  simp [h]

@[deprecated getElem_range' (since := "2024-06-12")]
theorem get_range' {n m step} (i) (H : i < (range' n m step).length) :
    get (range' n m step) ⟨i, H⟩ = n + step * i := by
  simp

set_option linter.deprecated false in
@[deprecated getElem?_range (since := "2024-06-12")]
theorem get?_range {m n : Nat} (h : m < n) : get? (range n) m = some m := by
  simp [getElem?_range, h]

@[deprecated getElem_range (since := "2024-06-12")]
theorem get_range {n} (i) (H : i < (range n).length) : get (range n) ⟨i, H⟩ = i := by
  simp

/-! ### indexOf and indexesOf -/

theorem foldrIdx_start :
    (xs : List α).foldrIdx f i s = (xs : List α).foldrIdx (fun i => f (i + s)) i := by
  induction xs generalizing f i s with
  | nil => rfl
  | cons h t ih =>
    dsimp [foldrIdx]
    simp only [@ih f]
    simp only [@ih (fun i => f (i + s))]
    simp [Nat.add_assoc, Nat.add_comm 1 s]

@[simp] theorem foldrIdx_cons :
    (x :: xs : List α).foldrIdx f i s = f s x (foldrIdx f i xs (s + 1)) := rfl

theorem findIdxs_cons_aux (p : α → Bool) :
    foldrIdx (fun i a is => if p a = true then (i + 1) :: is else is) [] xs s =
      map (· + 1) (foldrIdx (fun i a is => if p a = true then i :: is else is) [] xs s) := by
  induction xs generalizing s with
  | nil => rfl
  | cons x xs ih =>
    simp only [foldrIdx]
    split <;> simp [ih]

theorem findIdxs_cons :
    (x :: xs : List α).findIdxs p =
      bif p x then 0 :: (xs.findIdxs p).map (· + 1) else (xs.findIdxs p).map (· + 1) := by
  dsimp [findIdxs]
  rw [cond_eq_if]
  split <;>
  · simp only [Nat.zero_add, foldrIdx_start, Nat.add_zero, cons.injEq, true_and]
    apply findIdxs_cons_aux

@[simp] theorem indexesOf_nil [BEq α] : ([] : List α).indexesOf x = [] := rfl

theorem indexesOf_cons [BEq α] : (x :: xs : List α).indexesOf y =
    bif x == y then 0 :: (xs.indexesOf y).map (· + 1) else (xs.indexesOf y).map (· + 1) := by
  simp [indexesOf, findIdxs_cons]

@[simp] theorem eraseIdx_idxOf_eq_erase [BEq α] (a : α) (l : List α) :
    l.eraseIdx (l.idxOf a) = l.erase a := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    rw [List.erase, idxOf_cons]
    cases x == a <;> simp [ih]

@[deprecated (since := "2025-01-30")]
alias eraseIdx_indexOf_eq_erase := eraseIdx_idxOf_eq_erase

theorem idxOf_mem_indexesOf [BEq α] [LawfulBEq α] {xs : List α} (m : x ∈ xs) :
    xs.idxOf x ∈ xs.indexesOf x := by
  induction xs with
  | nil => simp_all
  | cons h t ih =>
    simp [idxOf_cons, indexesOf_cons, cond_eq_if]
    split <;> rename_i w
    · apply mem_cons_self
    · cases m
      case _ => simp_all
      case tail m =>
        specialize ih m
        simpa

@[deprecated (since := "2025-01-30")]
alias indexOf_mem_indexesOf := idxOf_mem_indexesOf

theorem idxOf_eq_idxOf? [BEq α] (a : α) (l : List α) :
    l.idxOf a = (match l.idxOf? a with | some i => i | none => l.length) := by
  simp [idxOf, idxOf?, findIdx_eq_findIdx?]

@[deprecated (since := "2025-01-30")]
alias indexOf_eq_indexOf? := idxOf_eq_idxOf?

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
        · simp only [nil_beq_iff, isEmpty_iff] at h₂
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
  simp only [isSuffixOf?, map_eq_some', isPrefixOf?_eq_some_iff_append_eq]
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

/-! ### deprecations -/

@[deprecated (since := "2024-08-15")] alias isEmpty_iff_eq_nil := isEmpty_iff

set_option linter.deprecated false in
@[deprecated getElem_eq_iff (since := "2024-06-12")]
theorem get_eq_iff : List.get l n = x ↔ l.get? n.1 = some x := by
  simp

set_option linter.deprecated false in
@[deprecated getElem?_inj (since := "2024-06-12")]
theorem get?_inj
    (h₀ : i < xs.length) (h₁ : Nodup xs) (h₂ : xs.get? i = xs.get? j) : i = j := by
  apply getElem?_inj h₀ h₁
  simp_all

@[deprecated (since := "2024-10-21")] alias modifyNth_nil := modify_nil
@[deprecated (since := "2024-10-21")] alias modifyNth_zero_cons := modify_zero_cons
@[deprecated (since := "2024-10-21")] alias modifyNth_succ_cons := modify_succ_cons
@[deprecated (since := "2024-10-21")] alias modifyNthTail_id := modifyTailIdx_id
@[deprecated (since := "2024-10-21")] alias eraseIdx_eq_modifyNthTail := eraseIdx_eq_modifyTailIdx
@[deprecated (since := "2024-10-21")] alias getElem?_modifyNth := getElem?_modify

set_option linter.deprecated false in
@[deprecated getElem?_modify (since := "2024-06-12")]
theorem get?_modifyNth (f : α → α) (n) (l : List α) (m) :
    (modify f n l).get? m = (fun a => if n = m then f a else a) <$> l.get? m := by
  simp [getElem?_modify]

@[deprecated (since := "2024-10-21")] alias length_modifyNthTail := length_modifyTailIdx
@[deprecated (since := "2024-06-07")] alias modifyNthTail_length := length_modifyTailIdx
@[deprecated (since := "2024-10-21")] alias modifyNthTail_add := modifyTailIdx_add
@[deprecated (since := "2024-10-21")] alias exists_of_modifyNthTail := exists_of_modifyTailIdx
@[deprecated (since := "2024-10-21")] alias length_modifyNth := length_modify
@[deprecated (since := "2024-06-07")] alias modifyNth_get?_length := length_modify
@[deprecated (since := "2024-10-21")] alias getElem?_modifyNth_eq := getElem?_modify_eq

set_option linter.deprecated false in
@[deprecated getElem?_modify_eq (since := "2024-06-12")]
theorem get?_modifyNth_eq (f : α → α) (n) (l : List α) :
    (modify f n l).get? n = f <$> l.get? n := by
  simp [getElem?_modify_eq]

@[deprecated (since := "2024-06-12")] alias getElem?_modifyNth_ne := getElem?_modify_ne

set_option linter.deprecated false in
@[deprecated getElem?_modify_ne (since := "2024-06-12")]
theorem get?_modifyNth_ne (f : α → α) {m n} (l : List α) (h : m ≠ n) :
    (modify f m l).get? n = l.get? n := by
  simp [h]

@[deprecated (since := "2024-10-21")] alias exists_of_modifyNth := exists_of_modify
@[deprecated (since := "2024-10-21")] alias modifyNthTail_eq_take_drop := modifyTailIdx_eq_take_drop
@[deprecated (since := "2024-10-21")] alias modifyNth_eq_take_drop := modify_eq_take_drop
@[deprecated (since := "2024-10-21")] alias modifyNth_eq_take_cons_drop := modify_eq_take_cons_drop
@[deprecated (since := "2024-10-21")] alias set_eq_modifyNth := set_eq_modify
@[deprecated (since := "2024-10-21")] alias modifyNth_eq_set_get? := modify_eq_set_get?
@[deprecated (since := "2024-10-21")] alias modifyNth_eq_set_get := modify_eq_set_get
-- The naming of `exists_of_set'` and `exists_of_set` have been swapped.
-- If no one complains, we will remove this version later.
@[deprecated exists_of_set (since := "2024-07-04")]
theorem exists_of_set' {l : List α} (h : n < l.length) :
    ∃ l₁ a l₂, l = l₁ ++ a :: l₂ ∧ l₁.length = n ∧ l.set n a' = l₁ ++ a' :: l₂ := by
  rw [set_eq_modify]; exact exists_of_modify _ h

set_option linter.deprecated false in
@[deprecated getElem?_set_self' (since := "2024-06-12")]
theorem get?_set_eq (a : α) (n) (l : List α) : (set l n a).get? n = (fun _ => a) <$> l.get? n := by
  simp only [get?_eq_getElem?, getElem?_set_self', Option.map_eq_map]
  rfl

set_option linter.deprecated false in
@[deprecated getElem?_set_eq_of_lt (since := "2024-06-12")]
theorem get?_set_eq_of_lt (a : α) {n} {l : List α} (h : n < length l) :
    (set l n a).get? n = some a := by
  rw [get?_eq_getElem?, getElem?_set_self', getElem?_eq_getElem h]; rfl

set_option linter.deprecated false in
@[deprecated getElem?_set_ne (since := "2024-06-12")]
theorem get?_set_ne (a : α) {m n} (l : List α) (h : m ≠ n) : (set l m a).get? n = l.get? n := by
  simp [h]

set_option linter.deprecated false in
@[deprecated getElem?_set (since := "2024-06-12")]
theorem get?_set (a : α) {m n} (l : List α) :
    (set l m a).get? n = if m = n then (fun _ => a) <$> l.get? n else l.get? n := by
  simp [getElem?_set']; rfl

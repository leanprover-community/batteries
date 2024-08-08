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

open Nat

/-! ### mem -/

@[simp] theorem mem_toArray {a : α} {l : List α} : a ∈ l.toArray ↔ a ∈ l := by
  simp [Array.mem_def]

/-! ### next? -/

@[simp] theorem next?_nil : @next? α [] = none := rfl
@[simp] theorem next?_cons (a l) : @next? α (a :: l) = some (a, l) := rfl

/-! ### get? -/

@[deprecated getElem_eq_iff (since := "2024-06-12")]
theorem get_eq_iff : List.get l n = x ↔ l.get? n.1 = some x := by
  simp

@[deprecated getElem?_inj (since := "2024-06-12")]
theorem get?_inj
    (h₀ : i < xs.length) (h₁ : Nodup xs) (h₂ : xs.get? i = xs.get? j) : i = j := by
  apply getElem?_inj h₀ h₁
  simp_all

/-! ### modifyNth -/

@[simp] theorem modifyNth_nil (f : α → α) (n) : [].modifyNth f n = [] := by cases n <;> rfl

@[simp] theorem modifyNth_zero_cons (f : α → α) (a : α) (l : List α) :
    (a :: l).modifyNth f 0 = f a :: l := rfl

@[simp] theorem modifyNth_succ_cons (f : α → α) (a : α) (l : List α) (n) :
    (a :: l).modifyNth f (n + 1) = a :: l.modifyNth f n := by rfl

theorem modifyNthTail_id : ∀ n (l : List α), l.modifyNthTail id n = l
  | 0, _ => rfl
  | _+1, [] => rfl
  | n+1, a :: l => congrArg (cons a) (modifyNthTail_id n l)

theorem eraseIdx_eq_modifyNthTail : ∀ n (l : List α), eraseIdx l n = modifyNthTail tail n l
  | 0, l => by cases l <;> rfl
  | n+1, [] => rfl
  | n+1, a :: l => congrArg (cons _) (eraseIdx_eq_modifyNthTail _ _)

@[deprecated (since := "2024-05-06")] alias removeNth_eq_nth_tail := eraseIdx_eq_modifyNthTail

theorem getElem?_modifyNth (f : α → α) :
    ∀ n (l : List α) m, (modifyNth f n l)[m]? = (fun a => if n = m then f a else a) <$> l[m]?
  | n, l, 0 => by cases l <;> cases n <;> simp
  | n, [], _+1 => by cases n <;> rfl
  | 0, _ :: l, m+1 => by cases h : l[m]? <;> simp [h, modifyNth, m.succ_ne_zero.symm]
  | n+1, a :: l, m+1 => by
    simp only [modifyNth_succ_cons, getElem?_cons_succ, Nat.reduceEqDiff, Option.map_eq_map]
    refine (getElem?_modifyNth f n l m).trans ?_
    cases h' : l[m]? <;> by_cases h : n = m <;>
      simp [h, if_pos, if_neg, Option.map, mt Nat.succ.inj, not_false_iff, h']

@[deprecated getElem?_modifyNth (since := "2024-06-12")]
theorem get?_modifyNth (f : α → α) (n) (l : List α) (m) :
    (modifyNth f n l).get? m = (fun a => if n = m then f a else a) <$> l.get? m := by
  simp [getElem?_modifyNth]

theorem modifyNthTail_length (f : List α → List α) (H : ∀ l, length (f l) = length l) :
    ∀ n l, length (modifyNthTail f n l) = length l
  | 0, _ => H _
  | _+1, [] => rfl
  | _+1, _ :: _ => congrArg (·+1) (modifyNthTail_length _ H _ _)

theorem modifyNthTail_add (f : List α → List α) (n) (l₁ l₂ : List α) :
    modifyNthTail f (l₁.length + n) (l₁ ++ l₂) = l₁ ++ modifyNthTail f n l₂ := by
  induction l₁ <;> simp [*, Nat.succ_add]

theorem exists_of_modifyNthTail (f : List α → List α) {n} {l : List α} (h : n ≤ l.length) :
    ∃ l₁ l₂, l = l₁ ++ l₂ ∧ l₁.length = n ∧ modifyNthTail f n l = l₁ ++ f l₂ :=
  have ⟨_, _, eq, hl⟩ : ∃ l₁ l₂, l = l₁ ++ l₂ ∧ l₁.length = n :=
    ⟨_, _, (take_append_drop n l).symm, length_take_of_le h⟩
  ⟨_, _, eq, hl, hl ▸ eq ▸ modifyNthTail_add (n := 0) ..⟩

@[simp] theorem modify_get?_length (f : α → α) : ∀ n l, length (modifyNth f n l) = length l :=
  modifyNthTail_length _ fun l => by cases l <;> rfl

@[simp] theorem getElem?_modifyNth_eq (f : α → α) (n) (l : List α) :
    (modifyNth f n l)[n]? = f <$> l[n]? := by
  simp only [getElem?_modifyNth, if_pos]

@[deprecated getElem?_modifyNth_eq (since := "2024-06-12")]
theorem get?_modifyNth_eq (f : α → α) (n) (l : List α) :
    (modifyNth f n l).get? n = f <$> l.get? n := by
  simp [getElem?_modifyNth_eq]

@[simp] theorem getElem?_modifyNth_ne (f : α → α) {m n} (l : List α) (h : m ≠ n) :
    (modifyNth f m l)[n]? = l[n]? := by
  simp only [getElem?_modifyNth, if_neg h, id_map']

@[deprecated getElem?_modifyNth_ne (since := "2024-06-12")]
theorem get?_modifyNth_ne (f : α → α) {m n} (l : List α) (h : m ≠ n) :
    (modifyNth f m l).get? n = l.get? n := by
  simp [h]

theorem exists_of_modifyNth (f : α → α) {n} {l : List α} (h : n < l.length) :
    ∃ l₁ a l₂, l = l₁ ++ a :: l₂ ∧ l₁.length = n ∧ modifyNth f n l = l₁ ++ f a :: l₂ :=
  match exists_of_modifyNthTail _ (Nat.le_of_lt h) with
  | ⟨_, _::_, eq, hl, H⟩ => ⟨_, _, _, eq, hl, H⟩
  | ⟨_, [], eq, hl, _⟩ => nomatch Nat.ne_of_gt h (eq ▸ append_nil _ ▸ hl)

theorem modifyNthTail_eq_take_drop (f : List α → List α) (H : f [] = []) :
    ∀ n l, modifyNthTail f n l = take n l ++ f (drop n l)
  | 0, _ => rfl
  | _ + 1, [] => H.symm
  | n + 1, b :: l => congrArg (cons b) (modifyNthTail_eq_take_drop f H n l)

theorem modifyNth_eq_take_drop (f : α → α) :
    ∀ n l, modifyNth f n l = take n l ++ modifyHead f (drop n l) :=
  modifyNthTail_eq_take_drop _ rfl

theorem modifyNth_eq_take_cons_drop (f : α → α) {n l} (h : n < length l) :
    modifyNth f n l = take n l ++ f l[n] :: drop (n + 1) l := by
  rw [modifyNth_eq_take_drop, drop_eq_getElem_cons h]; rfl

/-! ### set -/

theorem set_eq_modifyNth (a : α) : ∀ n (l : List α), set l n a = modifyNth (fun _ => a) n l
  | 0, l => by cases l <;> rfl
  | n+1, [] => rfl
  | n+1, b :: l => congrArg (cons _) (set_eq_modifyNth _ _ _)

theorem set_eq_take_cons_drop (a : α) {n l} (h : n < length l) :
    set l n a = take n l ++ a :: drop (n + 1) l := by
  rw [set_eq_modifyNth, modifyNth_eq_take_cons_drop _ h]

theorem modifyNth_eq_set_get? (f : α → α) :
    ∀ n (l : List α), l.modifyNth f n = ((fun a => l.set n (f a)) <$> l.get? n).getD l
  | 0, l => by cases l <;> rfl
  | n+1, [] => rfl
  | n+1, b :: l =>
    (congrArg (cons _) (modifyNth_eq_set_get? ..)).trans <| by cases h : l[n]? <;> simp [h]

theorem modifyNth_eq_set_get (f : α → α) {n} {l : List α} (h) :
    l.modifyNth f n = l.set n (f (l.get ⟨n, h⟩)) := by
  rw [modifyNth_eq_set_get?, get?_eq_get h]; rfl

-- The naming of `exists_of_set'` and `exists_of_set` have been swapped.
-- If no one complains, we will remove this version later.
@[deprecated exists_of_set (since := "2024-07-04")]
theorem exists_of_set' {l : List α} (h : n < l.length) :
    ∃ l₁ a l₂, l = l₁ ++ a :: l₂ ∧ l₁.length = n ∧ l.set n a' = l₁ ++ a' :: l₂ := by
  rw [set_eq_modifyNth]; exact exists_of_modifyNth _ h

@[deprecated getElem?_set_eq' (since := "2024-06-12")]
theorem get?_set_eq (a : α) (n) (l : List α) : (set l n a).get? n = (fun _ => a) <$> l.get? n := by
  simp

theorem getElem?_set_eq_of_lt (a : α) {n} {l : List α} (h : n < length l) :
    (set l n a)[n]? = some a := by rw [getElem?_set_eq', getElem?_eq_getElem h]; rfl

@[deprecated getElem?_set_eq_of_lt (since := "2024-06-12")]
theorem get?_set_eq_of_lt (a : α) {n} {l : List α} (h : n < length l) :
    (set l n a).get? n = some a := by
  rw [get?_eq_getElem?, getElem?_set_eq', getElem?_eq_getElem h]; rfl

@[deprecated getElem?_set_ne (since := "2024-06-12")]
theorem get?_set_ne (a : α) {m n} (l : List α) (h : m ≠ n) : (set l m a).get? n = l.get? n := by
  simp [h]

@[deprecated getElem?_set (since := "2024-06-12")]
theorem get?_set (a : α) {m n} (l : List α) :
    (set l m a).get? n = if m = n then (fun _ => a) <$> l.get? n else l.get? n := by
  simp [getElem?_set']

theorem get?_set_of_lt (a : α) {m n} (l : List α) (h : n < length l) :
    (set l m a).get? n = if m = n then some a else l.get? n := by
  simp [getElem?_set', getElem?_eq_getElem h]

theorem get?_set_of_lt' (a : α) {m n} (l : List α) (h : m < length l) :
    (set l m a).get? n = if m = n then some a else l.get? n := by
  simp [getElem?_set]; split <;> subst_vars <;> simp [*, getElem?_eq_getElem h]

@[deprecated (since := "2024-05-06")] alias length_removeNth := length_eraseIdx

/-! ### eraseP -/

@[simp] theorem extractP_eq_find?_eraseP
    (l : List α) : extractP p l = (find? p l, eraseP p l) := by
  let rec go (acc) : ∀ xs, l = acc.data ++ xs →
    extractP.go p l xs acc = (xs.find? p, acc.data ++ xs.eraseP p)
  | [] => fun h => by simp [extractP.go, find?, eraseP, h]
  | x::xs => by
    simp [extractP.go, find?, eraseP]; cases p x <;> simp
    · intro h; rw [go _ xs]; {simp}; simp [h]
  exact go #[] _ rfl

/-! ### erase -/

@[deprecated (since := "2024-04-22")] alias sublist.erase := Sublist.erase

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

theorem exists_of_replaceF : ∀ {l : List α} {a a'} (al : a ∈ l) (pa : p a = some a'),
    ∃ a a' l₁ l₂,
      (∀ b ∈ l₁, p b = none) ∧ p a = some a' ∧ l = l₁ ++ a :: l₂ ∧ l.replaceF p = l₁ ++ a' :: l₂
  | b :: l, a, a', al, pa =>
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
    exists_eq_right_right, mem_bind, iff_self]

/-! ### monadic operations -/

theorem forIn_eq_bindList [Monad m] [LawfulMonad m]
    (f : α → β → m (ForInStep β)) (l : List α) (init : β) :
    forIn l init f = ForInStep.run <$> (ForInStep.yield init).bindList f l := by
  induction l generalizing init <;> simp [*, map_eq_pure_bind]
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
  | [], l₂, _ => erase_sublist _ _
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

@[deprecated getElem?_range' (since := "2024-06-12")]
theorem get?_range' (s step) {m n : Nat} (h : m < n) :
    get? (range' s n step) m = some (s + step * m) := by
  simp [h]

@[deprecated getElem_range' (since := "2024-06-12")]
theorem get_range' {n m step} (i) (H : i < (range' n m step).length) :
    get (range' n m step) ⟨i, H⟩ = n + step * i := by
  simp

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

theorem indexOf_mem_indexesOf [BEq α] [LawfulBEq α] {xs : List α} (m : x ∈ xs) :
    xs.indexOf x ∈ xs.indexesOf x := by
  induction xs with
  | nil => simp_all
  | cons h t ih =>
    simp [indexOf_cons, indexesOf_cons, cond_eq_if]
    split <;> rename_i w
    · apply mem_cons_self
    · cases m
      case _ => simp_all
      case tail m =>
        specialize ih m
        simpa

theorem merge_loop_nil_left (s : α → α → Bool) (r t) :
    merge.loop s [] r t = reverseAux t r := by
  rw [merge.loop]

theorem merge_loop_nil_right (s : α → α → Bool) (l t) :
    merge.loop s l [] t = reverseAux t l := by
  cases l <;> rw [merge.loop]; intro; contradiction

theorem merge_loop (s : α → α → Bool) (l r t) :
    merge.loop s l r t = reverseAux t (merge s l r) := by
  rw [merge]; generalize hn : l.length + r.length = n
  induction n using Nat.recAux generalizing l r t with
  | zero =>
    rw [eq_nil_of_length_eq_zero (Nat.eq_zero_of_add_eq_zero_left hn)]
    rw [eq_nil_of_length_eq_zero (Nat.eq_zero_of_add_eq_zero_right hn)]
    simp only [merge.loop, reverseAux]
  | succ n ih =>
    match l, r with
    | [], r => simp only [merge_loop_nil_left]; rfl
    | l, [] => simp only [merge_loop_nil_right]; rfl
    | a::l, b::r =>
      simp only [merge.loop, cond]
      split
      · have hn : l.length + (b :: r).length = n := by
          apply Nat.add_right_cancel (m:=1)
          rw [←hn]; simp only [length_cons, Nat.add_succ, Nat.succ_add]
        rw [ih _ _ (a::t) hn, ih _ _ [] hn, ih _ _ [a] hn]; rfl
      · have hn : (a::l).length + r.length = n := by
          apply Nat.add_right_cancel (m:=1)
          rw [←hn]; simp only [length_cons, Nat.add_succ, Nat.succ_add]
        rw [ih _ _ (b::t) hn, ih _ _ [] hn, ih _ _ [b] hn]; rfl

@[simp] theorem merge_nil (s : α → α → Bool) (l) : merge s l [] = l := merge_loop_nil_right ..

@[simp] theorem nil_merge (s : α → α → Bool) (r) : merge s [] r = r := merge_loop_nil_left ..

theorem cons_merge_cons (s : α → α → Bool) (a b l r) :
  merge s (a::l) (b::r) = if s a b then a :: merge s l (b::r) else b :: merge s (a::l) r := by
  simp only [merge, merge.loop, cond]; split <;> (next hs => rw [hs, merge_loop]; rfl)

@[simp] theorem cons_merge_cons_pos (s : α → α → Bool) (l r) (h : s a b) :
    merge s (a::l) (b::r) = a :: merge s l (b::r) := by
  rw [cons_merge_cons, if_pos h]

@[simp] theorem cons_merge_cons_neg (s : α → α → Bool) (l r) (h : ¬ s a b) :
    merge s (a::l) (b::r) = b :: merge s (a::l) r := by
  rw [cons_merge_cons, if_neg h]

@[simp] theorem length_merge (s : α → α → Bool) (l r) :
    (merge s l r).length = l.length + r.length := by
  match l, r with
  | [], r => simp
  | l, [] => simp
  | a::l, b::r =>
    rw [cons_merge_cons]
    split
    · simp_arith [length_merge s l (b::r)]
    · simp_arith [length_merge s (a::l) r]

@[simp]
theorem mem_merge {s : α → α → Bool} : x ∈ merge s l r ↔ x ∈ l ∨ x ∈ r := by
  match l, r with
  | l, [] => simp
  | [], l => simp
  | a::l, b::r =>
    rw [cons_merge_cons]
    split
    · simp [mem_merge (l := l) (r := b::r), or_assoc]
    · simp [mem_merge (l := a::l) (r := r), or_assoc, or_left_comm]

theorem mem_merge_left (s : α → α → Bool) (h : x ∈ l) : x ∈ merge s l r :=
  mem_merge.2 <| .inl h

theorem mem_merge_right (s : α → α → Bool) (h : x ∈ r) : x ∈ merge s l r :=
  mem_merge.2 <| .inr h

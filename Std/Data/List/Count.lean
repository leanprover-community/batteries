/-
Copyright (c) 2014 Parikshit Khanna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Parikshit Khanna, Jeremy Avigad, Leonardo de Moura, Floris van Doorn, Mario Carneiro
-/
import Std.Data.List.Basic
import Std.Data.List.Lemmas

/-!
# Counting in lists

This file proves basic properties of `List.countp` and `List.count`, which count the number of
elements of a list satisfying a predicate and equal to a given element respectively. Their
definitions can be found in `Std.Data.List.Basic`.
-/


open Nat

namespace List

section Countp

variable (p q : α → Bool)

@[simp] theorem countp_nil : countp p [] = 0 := rfl

protected theorem countp_go_eq_add (l) : countp.go p l n = n + countp.go p l 0 := by
  induction l generalizing n with
  | nil => rfl
  | cons head tail ih =>
    unfold countp.go
    rw [ih (n := n + 1), ih (n := n), ih (n := 1)]
    by_cases h : p head
    · simp [h, Nat.add_assoc]
    · simp [h]

@[simp] theorem countp_cons_of_pos (l) (pa : p a) : countp p (a :: l) = countp p l + 1 := by
  have : countp.go p (a :: l) 0 = countp.go p l 1 := by
    suffices (bif _ then _ else _) = countp.go _ _ _ from this
    rw [pa]
    rfl
  unfold countp
  rw [this, Nat.add_comm, List.countp_go_eq_add]

@[simp] theorem countp_cons_of_neg (l) (pa : ¬p a) : countp p (a :: l) = countp p l := by
  simp [countp, countp.go, pa]

theorem countp_cons (a : α) (l) : countp p (a :: l) = countp p l + if p a then 1 else 0 := by
  by_cases h : p a <;> simp [h]

theorem length_eq_countp_add_countp (l) : length l = countp p l + countp (fun a => ¬p a) l := by
  induction l with
  | nil => rfl
  | cons x h ih =>
    by_cases h : p x
    · rw [countp_cons_of_pos _ _ h, countp_cons_of_neg _ _ _, length, ih]
      · rw [Nat.add_assoc, Nat.add_comm _ 1, Nat.add_assoc]
      · simp only [h]
    · rw [countp_cons_of_pos (fun a => ¬p a) _ _, countp_cons_of_neg _ _ h, length, ih]
      · rfl
      · simp only [h]

theorem countp_eq_length_filter (l) : countp p l = length (filter p l) := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    by_cases h : p x
    · rw [countp_cons_of_pos p l h, ih, filter_cons_of_pos l h, length]
    · rw [countp_cons_of_neg p l h, ih, filter_cons_of_neg l h]

theorem countp_le_length : countp p l ≤ l.length := by
  simp only [countp_eq_length_filter]
  apply length_filter_le

@[simp] theorem countp_append (l₁ l₂) : countp p (l₁ ++ l₂) = countp p l₁ + countp p l₂ := by
  simp only [countp_eq_length_filter, filter_append, length_append]

theorem countp_pos : 0 < countp p l ↔ ∃ a ∈ l, p a := by
  simp only [countp_eq_length_filter, length_pos_iff_exists_mem, mem_filter, exists_prop]

@[simp] theorem countp_eq_zero : countp p l = 0 ↔ ∀ a ∈ l, ¬p a := by
  simp only [countp_eq_length_filter, length_eq_zero, filter_eq_nil]

@[simp] theorem countp_eq_length : countp p l = l.length ↔ ∀ a ∈ l, p a := by
  rw [countp_eq_length_filter, filter_length_eq_length]

theorem length_filter_lt_length_iff_exists (l) :
    length (filter p l) < length l ↔ ∃ x ∈ l, ¬p x := by
  have := countp_pos (fun x => ¬p x) (l := l)
  simp [length_eq_countp_add_countp p l, countp_eq_length_filter] at this ⊢
  rw [←this]
  generalize length (filter p l) = x
  generalize length (filter _ _) = y
  rw [Nat.lt_add_right_iff_pos]

theorem Sublist.countp_le (s : l₁ <+ l₂) : countp p l₁ ≤ countp p l₂ := by
  simp only [countp_eq_length_filter]
  apply s.filter.length_le

@[simp] theorem countp_filter (l : List α) :
    countp p (filter q l) = countp (fun a => p a ∧ q a) l := by
  simp only [countp_eq_length_filter, filter_filter]

@[simp] theorem countp_true {l : List α} : (l.countp fun _ => true) = l.length := by simp

@[simp] theorem countp_false {l : List α} : (l.countp fun _ => false) = 0 := by simp

@[simp] theorem countp_map (p : β → Bool) (f : α → β) :
    ∀ l, countp p (map f l) = countp (p ∘ f) l
  | [] => rfl
  | a :: l => by rw [map_cons, countp_cons, countp_cons, countp_map p f l]; rfl

variable {p q}

theorem countp_mono_left (h : ∀ x ∈ l, p x → q x) : countp p l ≤ countp q l := by
  induction l with
  | nil => apply Nat.le_refl
  | cons a l ihl =>
    rw [forall_mem_cons] at h
    have ⟨ha, hl⟩ := h
    simp [countp_cons]
    cases h : p a
    . simp
      apply Nat.le_trans ?_ (Nat.le_add_right _ _)
      apply ihl hl
    . simp [ha h, Nat.add_one]
      apply Nat.succ_le_succ
      apply ihl hl

theorem countp_congr (h : ∀ x ∈ l, p x ↔ q x) : countp p l = countp q l :=
  Nat.le_antisymm
    (countp_mono_left fun x hx => (h x hx).1)
    (countp_mono_left fun x hx => (h x hx).2)

end Countp

/-! ### count -/

section Count

variable [DecidableEq α]

@[simp] theorem count_nil (a : α) : count a [] = 0 := rfl

theorem count_cons (a b : α) (l : List α) :
    count a (b :: l) = count a l + if a = b then 1 else 0 := by conv =>
  simp [count, countp_cons]
  lhs
  simp only [eq_comm]

@[simp] theorem count_cons_self (a : α) (l : List α) : count a (a :: l) = count a l + 1 := by
  simp [count_cons]

@[simp] theorem count_cons_of_ne (h : a ≠ b) (l : List α) : count a (b :: l) = count a l := by
  simp [count_cons, h]

theorem count_tail : ∀ (l : List α) (a : α) (h : 0 < l.length),
      l.tail.count a = l.count a - if a = get l ⟨0, h⟩ then 1 else 0
  | head :: tail, a, h => by simp [count_cons]

theorem count_le_length (a : α) (l : List α) : count a l ≤ l.length :=
  countp_le_length _

theorem Sublist.count_le (h : l₁ <+ l₂) (a : α) : count a l₁ ≤ count a l₂ :=
  h.countp_le _

theorem count_le_count_cons (a b : α) (l : List α) : count a l ≤ count a (b :: l) :=
  (sublist_cons _ _).count_le _

theorem count_singleton (a : α) : count a [a] = 1 := by
  simp [count_cons]

theorem count_singleton' (a b : α) : count a [b] = if a = b then 1 else 0 := by
  simp [count_cons]

@[simp] theorem count_append (a : α) : ∀ l₁ l₂, count a (l₁ ++ l₂) = count a l₁ + count a l₂ :=
  countp_append _

theorem count_concat (a : α) (l : List α) : count a (concat l a) = succ (count a l) := by simp

@[simp] theorem count_pos {a : α} {l : List α} : 0 < count a l ↔ a ∈ l := by
  simp only [count, countp_pos, beq_iff_eq, exists_eq_right]

@[simp]
theorem one_le_count_iff_mem {a : α} {l : List α} : 1 ≤ count a l ↔ a ∈ l := count_pos

theorem count_eq_zero_of_not_mem {a : α} {l : List α} (h : a ∉ l) : count a l = 0 :=
  Decidable.byContradiction fun h' => h <| count_pos.1 (Nat.pos_of_ne_zero h')

theorem not_mem_of_count_eq_zero {a : α} {l : List α} (h : count a l = 0) : a ∉ l :=
  fun h' => Nat.ne_of_lt (count_pos.2 h') h.symm

@[simp] theorem count_eq_zero {l : List α} : count a l = 0 ↔ a ∉ l :=
  ⟨not_mem_of_count_eq_zero, count_eq_zero_of_not_mem⟩

@[simp] theorem count_eq_length {l : List α} : count a l = l.length ↔ ∀ b ∈ l, a = b := by
  rw [count, countp_eq_length]
  refine ⟨fun h b hb => ?h₁, fun h b hb => ?h₂⟩
  · refine' Eq.symm _
    have := h b hb
    simp at this
    exact this
  · rw [h b hb, beq_self_eq_true]

@[simp] theorem count_replicate_self (a : α) (n : Nat) : count a (replicate n a) = n :=
  (count_eq_length.2 <| fun _ h => (eq_of_mem_replicate h).symm).trans (length_replicate ..)

theorem count_replicate (a b : α) (n : Nat) : count a (replicate n b) = if a = b then n else 0 := by
  split
  exacts [‹a = b› ▸ count_replicate_self .., count_eq_zero.2 <| mt eq_of_mem_replicate ‹a ≠ b›]

theorem filter_beq' (l : List α) (a : α) : l.filter (· == a) = replicate (count a l) a := by
  simp only [count, countp_eq_length_filter, eq_replicate, mem_filter, beq_iff_eq]
  exact ⟨trivial, fun _ h => h.2⟩

theorem filter_eq' (l : List α) (a : α) : l.filter (· = a) = replicate (count a l) a :=
  filter_beq' l a

theorem filter_eq (l : List α) (a : α) : l.filter (a = ·) = replicate (count a l) a := by
  have := filter_eq' l a
  simp only [eq_comm] at this ⊢
  exact this

theorem filter_beq (l : List α) (a : α) : l.filter (a == ·) = replicate (count a l) a :=
  filter_eq l a

theorem le_count_iff_replicate_sublist {l : List α} : n ≤ count a l ↔ replicate n a <+ l :=
  ⟨fun h =>
    ((replicate_sublist_replicate a).2 h).trans <| filter_eq l a ▸ filter_sublist _,
    fun h => by
      have := h.count_le a
      simp only [count_replicate_self] at this ⊢
      exact this⟩

theorem replicate_count_eq_of_count_eq_length {l : List α} (h : count a l = length l) :
    replicate (count a l) a = l :=
  (le_count_iff_replicate_sublist.mp (Nat.le_refl _)).eq_of_length <|
    (length_replicate (count a l) a).trans h

@[simp] theorem count_filter {l : List α} (h : p a) : count a (filter p l) = count a l := by
  rw [count, countp_filter]
  congr
  funext b
  rw [(by rfl : (b == a) = decide (b = a))]
  rw [decide_eq_decide]
  simp; intro heq; exact heq ▸ h

theorem count_le_count_map [DecidableEq β] (l : List α) (f : α → β) (x : α) :
    count x l ≤ count (f x) (map f l) := by
  rw [count, count, countp_map]
  exact countp_mono_left <| by simp (config := {contextual := true})

theorem count_erase (a b : α) :
    ∀ l : List α, count a (l.erase b) = count a l - if a = b then 1 else 0
  | [] => by simp
  | c :: l => by
    rw [erase_cons]
    by_cases hc : c = b
    · rw [if_pos hc, hc, count_cons, Nat.add_sub_cancel]
    · rw [if_neg hc, count_cons, count_cons, count_erase a b l]
      by_cases ha : a = b
      · rw [← ha, eq_comm] at hc
        rw [if_pos ha, if_neg hc, Nat.add_zero, Nat.add_zero]
      · rw [if_neg ha, Nat.sub_zero, Nat.sub_zero]

@[simp] theorem count_erase_self (a : α) (l : List α) : count a (List.erase l a) = count a l - 1 := by
  rw [count_erase, if_pos rfl]

@[simp] theorem count_erase_of_ne (ab : a ≠ b) (l : List α) : count a (l.erase b) = count a l :=
  by rw [count_erase, if_neg ab, Nat.sub_zero]

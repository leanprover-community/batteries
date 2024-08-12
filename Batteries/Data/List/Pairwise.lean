/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, James Gallicchio
-/
import Batteries.Data.List.Count

/-!
# Pairwise relations on a list

This file provides basic results about `List.Pairwise` and `List.pwFilter` (definitions are in
`Batteries.Data.List.Basic`).
`Pairwise r [a 0, ..., a (n - 1)]` means `∀ i j, i < j → r (a i) (a j)`. For example,
`Pairwise (≠) l` means that all elements of `l` are distinct, and `Pairwise (<) l` means that `l`
is strictly increasing.
`pwFilter r l` is the list obtained by iteratively adding each element of `l` that doesn't break
the pairwiseness of the list we have so far. It thus yields `l'` a maximal sublist of `l` such that
`Pairwise r l'`.

## Tags

sorted, nodup
-/


open Nat Function

namespace List

/-! ### Pairwise -/

@[deprecated pairwise_iff_forall_sublist (since := "2023-09-18")]
theorem pairwise_of_reflexive_on_dupl_of_forall_ne [DecidableEq α] {l : List α} {r : α → α → Prop}
    (hr : ∀ a, 1 < count a l → r a a) (h : ∀ a ∈ l, ∀ b ∈ l, a ≠ b → r a b) : l.Pairwise r := by
  apply pairwise_iff_forall_sublist.mpr
  intro a b hab
  if heq : a = b then
    cases heq; apply hr
    rwa [show [a,a] = replicate 2 a from rfl, ← le_count_iff_replicate_sublist] at hab
  else
    apply h <;> try (apply hab.subset; simp)
    exact heq

theorem pairwise_iff_get : Pairwise R l ↔ ∀ (i j) (_hij : i < j), R (get l i) (get l j) := by
  rw [pairwise_iff_getElem]
  constructor <;> intro h
  · intros i j h'
    exact h _ _ _ _ h'
  · intros i j hi hj h'
    exact h ⟨i, hi⟩ ⟨j, hj⟩ h'

/-! ### Pairwise filtering -/

@[simp] theorem pwFilter_nil [DecidableRel R] : pwFilter R [] = [] := rfl

@[simp] theorem pwFilter_cons_of_pos [DecidableRel (α := α) R] {a : α} {l : List α}
    (h : ∀ b ∈ pwFilter R l, R a b) : pwFilter R (a :: l) = a :: pwFilter R l := if_pos h

@[simp] theorem pwFilter_cons_of_neg [DecidableRel (α := α) R] {a : α} {l : List α}
    (h : ¬∀ b ∈ pwFilter R l, R a b) : pwFilter R (a :: l) = pwFilter R l := if_neg h

theorem pwFilter_map [DecidableRel (α := α) R] (f : β → α) :
    ∀ l : List β, pwFilter R (map f l) = map f (pwFilter (fun x y => R (f x) (f y)) l)
  | [] => rfl
  | x :: xs => by
    if h : ∀ b ∈ pwFilter R (map f xs), R (f x) b then
      have h' : ∀ b : β, b ∈ pwFilter (fun x y : β => R (f x) (f y)) xs → R (f x) (f b) :=
        fun b hb => h _ (by rw [pwFilter_map f xs]; apply mem_map_of_mem _ hb)
      rw [map, pwFilter_cons_of_pos h, pwFilter_cons_of_pos h', pwFilter_map f xs, map]
    else
      rw [map, pwFilter_cons_of_neg h, pwFilter_cons_of_neg ?_, pwFilter_map f xs]
      refine fun hh => h fun a ha => ?_
      rw [pwFilter_map f xs, mem_map] at ha
      let ⟨b, hb₀, hb₁⟩ := ha; exact hb₁ ▸ hh _ hb₀

theorem pwFilter_sublist [DecidableRel (α := α) R] : ∀ l : List α, pwFilter R l <+ l
  | [] => nil_sublist _
  | x :: l =>
    if h : ∀ y ∈ pwFilter R l, R x y then
      pwFilter_cons_of_pos h ▸ (pwFilter_sublist l).cons₂ _
    else
      pwFilter_cons_of_neg h ▸ Sublist.cons _ (pwFilter_sublist l)

theorem pwFilter_subset [DecidableRel (α := α) R] (l : List α) : pwFilter R l ⊆ l :=
  (pwFilter_sublist _).subset

theorem pairwise_pwFilter [DecidableRel (α := α) R] : ∀ l : List α, Pairwise R (pwFilter R l)
  | [] => Pairwise.nil
  | x :: l =>
    if h : ∀ y ∈ pwFilter R l, R x y then
      pwFilter_cons_of_pos h ▸ pairwise_cons.2 ⟨h, pairwise_pwFilter l⟩
    else
      pwFilter_cons_of_neg h ▸ pairwise_pwFilter l

theorem pwFilter_eq_self [DecidableRel (α := α) R] {l : List α} :
    pwFilter R l = l ↔ Pairwise R l := by
  refine ⟨fun e => e ▸ pairwise_pwFilter l, fun p => ?_⟩
  induction l with
  | nil => rfl
  | cons x l IH =>
    let ⟨al, p⟩ := pairwise_cons.1 p
    rw [pwFilter_cons_of_pos fun b hb => ?_, IH p]
    rw [IH p] at hb
    exact al _ hb

@[simp] theorem pwFilter_idem [DecidableRel (α := α) R] :
    pwFilter R (pwFilter R l) = pwFilter R l := pwFilter_eq_self.2 (pairwise_pwFilter ..)

theorem forall_mem_pwFilter [DecidableRel (α := α) R]
    (neg_trans : ∀ {x y z}, R x z → R x y ∨ R y z) (a : α) (l : List α) :
    (∀ b ∈ pwFilter R l, R a b) ↔ ∀ b ∈ l, R a b := by
  refine ⟨?_, fun h b hb => h _ <| pwFilter_subset (R := R) _ hb⟩
  induction l with
  | nil => exact fun _ _ h => (not_mem_nil _ h).elim
  | cons x l IH =>
    simp only [forall_mem_cons]
    if h : ∀ y ∈ pwFilter R l, R x y then
      simpa [pwFilter_cons_of_pos h] using fun r H => ⟨r, IH H⟩
    else
      refine pwFilter_cons_of_neg h ▸ fun H => ⟨?_, IH H⟩
      match e : find? (fun y => ¬R x y) (pwFilter R l) with
      | none => exact h.elim fun y hy => by simpa using find?_eq_none.1 e y hy
      | some k =>
        have := find?_some e
        apply (neg_trans (H k (mem_of_find?_eq_some e))).resolve_right
        rw [decide_eq_true_iff] at this; exact this

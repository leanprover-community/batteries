/-
Copyright (c) 2024 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: François G. Dorais
-/
import Batteries.Data.Array.Lemmas
import Batteries.Data.List.Pairwise

namespace Array

/--
`Pairwise R as` means that all the elements of the array `as` are `R`-related to all elements with
larger indices.

`Pairwise R #[1, 2, 3] ↔ R 1 2 ∧ R 1 3 ∧ R 2 3`

For example `as.Pairwise (· ≠ ·)` asserts that `as` has no duplicates, `as.Pairwise (· < ·)` asserts
that `as` is strictly sorted and `as.Pairwise (· ≤ ·)` asserts that `as` is weakly sorted.
-/
def Pairwise (R : α → α → Prop) (as : Array α) : Prop := as.toList.Pairwise R

theorem pairwise_iff_getElem {as : Array α} : as.Pairwise R ↔
    ∀ (i j : Nat) (_ : i < as.size) (_ : j < as.size), i < j → R as[i] as[j] := by
  unfold Pairwise; simp [List.pairwise_iff_getElem, length_toList]

@[deprecated (since := "2025-02-19")] alias pairwise_iff_get := pairwise_iff_getElem

instance (R : α → α → Prop) [DecidableRel R] (as) : Decidable (Pairwise R as) :=
  have : (∀ (j : Fin as.size) (i : Fin j.val), R as[i.val] (as[j.val])) ↔ Pairwise R as := by
    rw [pairwise_iff_getElem]
    constructor
    · intro h i j _ hj hlt; exact h ⟨j, hj⟩ ⟨i, hlt⟩
    · intro h ⟨j, hj⟩ ⟨i, hlt⟩; exact h i j (Nat.lt_trans hlt hj) hj hlt
  decidable_of_iff _ this

theorem pairwise_empty : #[].Pairwise R := by
  unfold Pairwise; exact List.Pairwise.nil

theorem pairwise_singleton (R : α → α → Prop) (a) : #[a].Pairwise R := by
  unfold Pairwise; exact List.pairwise_singleton ..

theorem pairwise_pair : #[a, b].Pairwise R ↔ R a b := by
  unfold Pairwise; exact List.pairwise_pair

theorem pairwise_append {as bs : Array α} :
    (as ++ bs).Pairwise R ↔ as.Pairwise R ∧ bs.Pairwise R ∧ (∀ x ∈ as, ∀ y ∈ bs, R x y) := by
  unfold Pairwise; simp [← mem_toList, toList_append, ← List.pairwise_append]

theorem pairwise_push {as : Array α} :
    (as.push a).Pairwise R ↔ as.Pairwise R ∧ (∀ x ∈ as, R x a) := by
  unfold Pairwise
  simp [← mem_toList, push_toList, List.pairwise_append, List.pairwise_singleton,
    List.mem_singleton]

theorem pairwise_extract {as : Array α} (h : as.Pairwise R) (start stop) :
    (as.extract start stop).Pairwise R := by
  simp only [pairwise_iff_getElem, getElem_extract, size_extract] at h ⊢
  intro _ _ _ _ hlt
  apply h
  exact Nat.add_lt_add_left hlt start

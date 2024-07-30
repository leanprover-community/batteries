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
def Pairwise (R : α → α → Prop) (as : Array α) : Prop := as.data.Pairwise R

-- TODO: add efficient decidable instance

theorem pairwise_defFin {as : Array α} : as.Pairwise R ↔
    ∀ (i j : Fin as.size) (_ : i < j), R as[i] as[j] := by
  unfold Pairwise; simp [List.pairwise_iff_get, getElem_fin_eq_data_get]; rfl

theorem pairwise_defNat {as : Array α} : as.Pairwise R ↔
    ∀ (i j : Nat) (_ : i < as.size) (_ : j < as.size) (_ : i < j), R as[i] as[j] := by
  unfold Pairwise; simp [List.pairwise_iff_getElem, data_length]; rfl

theorem pairwise_empty : #[].Pairwise R := by
  unfold Pairwise; exact List.Pairwise.nil

theorem pairwise_singleton (R : α → α → Prop) (a) : #[a].Pairwise R := by
  unfold Pairwise; exact List.pairwise_singleton ..

theorem pairwise_pair : #[a, b].Pairwise R ↔ R a b := by
  unfold Pairwise; exact List.pairwise_pair

theorem pairwise_append {as bs : Array α} :
    (as ++ bs).Pairwise R ↔ as.Pairwise R ∧ bs.Pairwise R ∧ (∀ x ∈ as, ∀ y ∈ bs, R x y) := by
  unfold Pairwise; simp [← mem_data, append_data, ← List.pairwise_append]

theorem pairwise_push {as : Array α} :
    (as.push a).Pairwise R ↔ as.Pairwise R ∧ (∀ x ∈ as, R x a) := by
  unfold Pairwise
  simp [← mem_data, push_data, List.pairwise_append, List.pairwise_singleton, List.mem_singleton]

theorem pairwise_extract {as : Array α} (h : as.Pairwise R) (start stop) :
    (as.extract start stop).Pairwise R := by
  simp only [pairwise_defNat, get_extract, size_extract] at h ⊢
  intro _ _ _ _ hlt
  apply h
  exact Nat.add_lt_add_left hlt start

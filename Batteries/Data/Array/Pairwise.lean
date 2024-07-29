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
abbrev Pairwise (R : α → α → Prop) (as : Array α) : Prop :=
  ∀ (i j : Fin as.size), i < j → R as[i] as[j]

theorem pairwise_data {as : Array α} : as.data.Pairwise R ↔ as.Pairwise R := by
  simp [Pairwise, List.pairwise_iff_get, List.get_eq_getElem, data_length, getElem_eq_data_getElem]

theorem pairwise_iff_getElem {as : Array α} : as.Pairwise R ↔
    ∀ (i j : Nat) (_ : i < as.size) (_ : j < as.size) (_ : i < j), R as[i] as[j] := by
  constructor
  · intro h i j hi hj hij; exact h ⟨i, hi⟩ ⟨j, hj⟩ hij
  · intro h ⟨i, hi⟩ ⟨j, hj⟩ hij; exact h i j hi hj hij

theorem pairwise_empty : #[].Pairwise R := by
  rw [← pairwise_data]; exact List.Pairwise.nil

theorem pairwise_singleton (R : α → α → Prop) (a) : #[a].Pairwise R := by
  rw [← pairwise_data]; exact List.pairwise_singleton ..

theorem pairwise_pair : #[a, b].Pairwise R ↔ R a b := by
  rw [← pairwise_data]; exact List.pairwise_pair

theorem pairwise_append {as bs : Array α} :
    (as ++ bs).Pairwise R ↔ as.Pairwise R ∧ bs.Pairwise R ∧ (∀ x ∈ as, ∀ y ∈ bs, R x y) := by
  simp [← pairwise_data, ← mem_data, append_data, ← List.pairwise_append]

theorem pairwise_push {as : Array α} :
    (as.push a).Pairwise R ↔ as.Pairwise R ∧ (∀ x ∈ as, R x a) := by
  simp [← pairwise_data, ← mem_data, push_data, List.pairwise_append, List.pairwise_singleton,
    List.mem_singleton]

theorem pairwise_extract {as : Array α} (h : as.Pairwise R) (start stop) :
    (as.extract start stop).Pairwise R := by
  intro _ _ hlt
  simp only [Fin.getElem_fin, get_extract]
  rw [pairwise_iff_getElem] at h
  apply h; exact Nat.add_lt_add_left hlt start

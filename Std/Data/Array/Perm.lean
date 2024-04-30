/-
Copyright (c) 2024 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Mario Carneiro
-/
import Std.Data.Array.Lemmas
import Std.Data.List.Perm

namespace Array
open List

theorem swap_of_append_right (as : Array α)
  {A B b C} {i j} (hi : A.length = i.1) (hj : i.1 + B.length = j.1)
    (eq1 : as.data = A ++ B ++ b :: C) :
    ∃ B', B' ~ B ∧ (as.swap i j).data = A ++ b :: B' ++ C := by
  match B with
  | [] => exact ⟨[], .rfl, by cases Fin.ext hj; simp [swap_self, eq1]⟩
  | a :: B =>
    refine ⟨B ++ [a], perm_append_comm, ?_⟩
    simpa using swap_of_append as hi (by simpa using hj) eq1

theorem swap_of_append_left (as : Array α)
  {A a B C} {i j} (hi : A.length = i.1) (hj : i.1 + B.length = j.1)
    (eq1 : as.data = A ++ a :: B ++ C) :
    ∃ B', B' ~ B ∧ (as.swap i j).data = A ++ B' ++ a :: C := by
  obtain rfl | ⟨B, b, rfl⟩ := eq_nil_or_concat B
  · exact ⟨[], .rfl, by cases Fin.ext hj; simp [swap_self, eq1]⟩
  · refine ⟨b :: B, perm_append_comm (l₁ := [_]), ?_⟩
    exact swap_of_append as hi (by simpa using hj) (by simp [eq1])

theorem swap_perm (as : Array α) (i j : Fin as.size) : (as.swap i j).data ~ as.data := by
  have {i j} (ij : i < j) : (as.swap i j).data ~ as.data := by
    have ⟨A, a, B, b, C, h1, h2, eq⟩ := exists_three_of_lt _ ij j.2
    rw [eq, swap_of_append as h1 h2 eq, List.append_assoc, List.append_assoc]
    exact .append_left _ <| perm_middle.trans <| .cons _ perm_middle.symm
  obtain h | h | h := Nat.lt_trichotomy i j
  · exact this h
  · rw [Fin.eq_of_val_eq h, swap_self]
  · rw [swap_comm]; exact this h

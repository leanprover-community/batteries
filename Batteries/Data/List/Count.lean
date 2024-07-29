/-
Copyright (c) 2014 Parikshit Khanna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Parikshit Khanna, Jeremy Avigad, Leonardo de Moura, Floris van Doorn, Mario Carneiro
-/
import Batteries.Data.List.Basic
import Batteries.Data.List.Lemmas

/-!
# Counting in lists

This file proves basic properties of `List.countP` and `List.count`, which count the number of
elements of a list satisfying a predicate and equal to a given element respectively. Their
definitions can be found in `Batteries.Data.List.Basic`.
-/


open Nat

namespace List


/-! ### count -/

section count

variable [DecidableEq α]

theorem count_singleton' (a b : α) : count a [b] = if b = a then 1 else 0 := by simp [count_cons]

theorem count_concat (a : α) (l : List α) : count a (concat l a) = succ (count a l) := by simp

@[deprecated filter_eq (since := "2023-12-14")]
theorem filter_eq' (l : List α) (a : α) : l.filter (a = ·) = replicate (count a l) a := by
  simpa only [eq_comm] using filter_eq l a

@[deprecated filter_beq (since := "2023-12-14")]
theorem filter_beq' (l : List α) (a : α) : l.filter (a == ·) = replicate (count a l) a := by
  simpa only [eq_comm (b := a)] using filter_eq l a

/-
Copyright (c) 2021 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Mario Carneiro, Gabriel Ebner
-/
module

public import Batteries.Data.Array.Basic
public import Batteries.Data.List.Lemmas

@[expose] public section

namespace Array

/-! ### equalSet -/

@[simp] theorem equalSet_eq_true [BEq α] [LawfulBEq α] (xs ys : Array α) :
    xs.equalSet ys = true ↔ ∀ a, a ∈ xs ↔ a ∈ ys := by
    simp [equalSet]
    constructor
    ·
      intro h a
      have h_xs := h.left
      have h_ys := h.right
      constructor
      all_goals
        intro a_in_ss
        have h_ss_idx := Array.mem_iff_getElem.mp a_in_ss
        obtain ⟨i, h_i_lt_size, h_a_eq_get⟩ := h_ss_idx
      ·
        specialize h_xs i h_i_lt_size
        simp [←h_a_eq_get, h_xs]
      ·
        specialize h_ys i h_i_lt_size
        simp [←h_a_eq_get, h_ys]
    ·
      intro h
      constructor
      all_goals
        intro i h_i_lt_size
        first
          | apply fun (a : α) => (h a).mp
          | apply fun (a : α) => (h a).mpr
        exact Array.getElem_mem h_i_lt_size


/-! ### idxOf? -/

@[grind =]
theorem idxOf?_toList [BEq α] {a : α} {l : Array α} :
    l.toList.idxOf? a = l.idxOf? a := by
  rcases l with ⟨l⟩
  simp

/-! ### erase -/

@[simp, grind =] theorem toList_erase [BEq α] (l : Array α) (a : α) :
    (l.erase a).toList = l.toList.erase a := by
  rcases l with ⟨l⟩
  simp

@[simp] theorem size_eraseIdxIfInBounds (a : Array α) (i : Nat) :
    (a.eraseIdxIfInBounds i).size = if i < a.size then a.size-1 else a.size := by
  grind

theorem toList_drop (as: Array α) (n : Nat) :
    (as.drop n).toList = as.toList.drop n := by
  simp only [drop, toList_extract, size_eq_length_toList, List.drop_eq_extract]

/-! ### set -/

/-! ### map -/

/-! ### mem -/

/-! ### insertAt -/

/-! ### extract -/

@[simp] theorem extract_empty_of_start_eq_stop {a : Array α} :
    a.extract i i = #[] := by grind

theorem extract_append_of_stop_le_size_left {a b : Array α} (h : j ≤ a.size) :
    (a ++ b).extract i j = a.extract i j := by grind

theorem extract_append_of_size_left_le_start {a b : Array α} (h : a.size ≤ i) :
    (a ++ b).extract i j = b.extract (i - a.size) (j - a.size) := by
  rw [extract_append]; grind

theorem extract_eq_of_size_le_stop {a : Array α} (h : a.size ≤ j) :
    a.extract i j = a.extract i := by grind

/-! ### swapIfInBounds -/
@[simp, grind =] theorem toList_swapIfInBounds {a : Array α} :
    (a.swapIfInBounds i j).toList = a.toList.swap i j := List.ext_getElem (by simp) (by grind)

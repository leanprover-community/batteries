/-
Copyright (c) 2024 Bulhwi Cha, Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bulhwi Cha, Mario Carneiro
-/
import Std.Data.List.Lemmas

namespace List

/-- Returns `(l₁, l₂)` for the first split `l = l₁ ++ l₂` such that `P l₂` returns true. -/
def splitOnceRightP (P : List α → Bool) (l : List α) : Option (List α × List α) :=
  if P l then
    some ([], l)
  else
    match l with
    | [] => none
    | a :: l => (splitOnceRightP P l).map fun (l, r) => (a :: l, r)

theorem eq_append_of_splitOnceRightP (P : List α → Bool) (l : List α) :
    ∀ l₁ l₂, splitOnceRightP P l = some (l₁, l₂) → l = l₁ ++ l₂ := by
  induction l with
  | nil => simp [splitOnceRightP]
  | cons a l ih =>
    if h : P (a :: l) then
      simp [splitOnceRightP, h]
    else
      simp only [splitOnceRightP, h, ite_false]
      match e : splitOnceRightP P l with
      | none => simp
      | some (lf, rt) => simp; apply ih; assumption

theorem P_of_splitOnceRightP (P : List α → Bool) (l : List α) :
    ∀ l₁ l₂, splitOnceRightP P l = some (l₁, l₂) → P l₂ := by
  induction l with
  | nil => simp [splitOnceRightP]
  | cons a l ih =>
    if h : P (a :: l) then
      simp [splitOnceRightP, h]
    else
      simp only [splitOnceRightP, h, ite_false]
      match e : splitOnceRightP P l with
      | none => simp
      | some (lf, rt) => simp; apply ih; assumption

/--
Split a list at every occurrence of a separator list. The separators are not in the result.
```
[1, 1, 2, 3, 2, 4, 4].splitOnList [2, 3] = [[1, 1], [2, 4, 4]]
```
-/
def splitOnList [BEq α] (l sep : List α) : List (List α) :=
  if h : sep.isEmpty then
    [l]
  else
    match e : splitOnceRightP sep.isPrefixOf l with
    | none => [l]
    | some (l₁, l₂) =>
      have : length l₂ - sep.length < length l := by
        rw [eq_append_of_splitOnceRightP (sep.isPrefixOf) l l₁ l₂ e, length_append]
        calc
          length l₂ - length sep < length l₂ := by
            apply Nat.sub_lt_self
            · apply length_pos.mpr; simp [← isEmpty_iff_eq_nil, h]
            · apply length_le_of_isPrefixOf (P_of_splitOnceRightP sep.isPrefixOf l l₁ l₂ e)
          _ ≤ length l₁ + length l₂ := Nat.le_add_left ..
      splitOnList (l₂.drop sep.length) sep
termination_by _ => l.length

end List

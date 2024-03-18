/-
Copyright (c) 2024 Bulhwi Cha, Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bulhwi Cha, Mario Carneiro
-/
import Std.Data.List.Lemmas

/-!
# `List.splitOnList`

This file introduces the `List.splitOnList` function, which is a specification for `String.splitOn`.
We need it to prove `String.splitOn_of_valid` in `Std.Data.String.Lemmas`.
```
[1, 1, 2, 3, 2, 4, 4].splitOnList []     = [[1, 1, 2, 3, 2, 4, 4]]
[1, 1, 2, 3, 2, 4, 4].splitOnList [5, 6] = [[1, 1, 2, 3, 2, 4, 4]]
[1, 1, 2, 3, 2, 4, 4].splitOnList [2, 3] = [[1, 1], [2, 4, 4]]
```
-/

namespace List

/-- Returns `(l₁, l₂)` for the first split `l = l₁ ++ l₂` such that `P l₂` returns true. -/
def splitOnceRightP (P : List α → Bool) (l : List α) : Option (List α × List α) :=
  if P l then
    some ([], l)
  else
    match l with
    | [] => none
    | a::l => (splitOnceRightP P l).map fun (l, r) => (a :: l, r)

theorem splitOnceRightP_of_P {P : List α → Bool} {l} (h : P l) :
    splitOnceRightP P l = some ([], l) := by
  unfold splitOnceRightP
  simp [h]

theorem splitOnceRight_nil (P : List α → Bool) :
    splitOnceRightP P [] = if P [] then some ([], []) else none :=
  rfl

theorem splitOnceRight_of_ne_nil_of_not_P {P : List α → Bool} {l} (hne : l ≠ []) (hnp : ¬P l) :
    splitOnceRightP P l = (splitOnceRightP P l.tail).map fun (lf, rt) => (l.head hne :: lf, rt) :=
      by
  obtain ⟨a, l, rfl⟩ := exists_cons_of_ne_nil hne
  conv => lhs; unfold splitOnceRightP
  simp [hnp]

theorem eq_append_of_splitOnceRightP {P : List α → Bool} {l} :
    ∀ l₁ l₂, splitOnceRightP P l = some (l₁, l₂) → l = l₁ ++ l₂ := by
  induction l with
  | nil => simp [splitOnceRightP]
  | cons a l ih =>
    if h : P (a :: l) then
      simp [splitOnceRightP, h]
    else
      simp only [splitOnceRightP, h]
      match e : splitOnceRightP P l with
      | none => simp
      | some (lf, rt) => simp; apply ih; assumption

theorem P_of_splitOnceRightP {P : List α → Bool} {l} :
    ∀ l₁ l₂, splitOnceRightP P l = some (l₁, l₂) → P l₂ := by
  induction l with
  | nil => simp [splitOnceRightP]
  | cons a l ih =>
    if h : P (a :: l) then
      simp [splitOnceRightP, h]
    else
      simp only [splitOnceRightP, h]
      match e : splitOnceRightP P l with
      | none => simp
      | some (lf, rt) => simp; apply ih; assumption

variable [BEq α] [LawfulBEq α]

theorem splitOnceRightP_isPrefixOf_eq_none_of_length_lt {l sep : List α}
    (h : l.length < sep.length) : splitOnceRightP sep.isPrefixOf l = none := by
  have not_isPrefixOf_of_length_lt {l} (h : l.length < sep.length) : ¬sep.isPrefixOf l := by
    rw [← IsPrefix.iff_isPrefixOf]
    exact mt IsPrefix.length_le (Nat.not_le_of_lt h)
  induction l with
  | nil => unfold splitOnceRightP; simp [not_isPrefixOf_of_length_lt h]
  | cons a l ih =>
    unfold splitOnceRightP
    simp only [not_isPrefixOf_of_length_lt h, ↓reduceIte, Option.map_eq_none']
    have h' : l.length < sep.length :=
      calc
        l.length < (a :: l).length := by simp
        _ < sep.length := h
    exact ih h'

/--
Split a list at every occurrence of a separator list. The separators are not in the result.
```
[1, 1, 2, 3, 2, 4, 4].splitOnList [2, 3] = [[1, 1], [2, 4, 4]]
```
-/
def splitOnList (l sep : List α) : List (List α) :=
  if h : sep.isEmpty then
    [l]
  else
    match e : splitOnceRightP sep.isPrefixOf l with
    | none => [l]
    | some (l₁, l₂) =>
      have : l₂.length - sep.length < l.length := by
        rw [eq_append_of_splitOnceRightP l₁ l₂ e, length_append]
        calc
          l₂.length - sep.length < l₂.length := Nat.sub_lt_self (by simp [length_pos,
            ← isEmpty_iff_eq_nil, h]) (IsPrefix.length_le <| IsPrefix.iff_isPrefixOf.mpr
            (P_of_splitOnceRightP l₁ l₂ e))
          _ ≤ l₁.length + l₂.length := Nat.le_add_left ..
      l₁ :: splitOnList (l₂.drop sep.length) sep
termination_by l.length

theorem splitOnList_nil_left (sep : List α) : splitOnList [] sep = [[]] := by
  cases sep <;> rfl

theorem splitOnList_nil_right (l : List α) : splitOnList l [] = [l] := by
  simp [splitOnList]

theorem splitOnList_append_append_of_isPrefixOf {l : List α} (sep₁) {sep₂} (hsp₂ : sep₂ ≠ [])
    (hpf : sep₂.isPrefixOf l) :
    splitOnList (sep₁ ++ l) (sep₁ ++ sep₂) =
      [] :: splitOnList (l.drop sep₂.length) (sep₁ ++ sep₂) := by
  have hnem : ¬(sep₁ ++ sep₂).isEmpty := by simp [isEmpty_iff_eq_nil, hsp₂]
  have hpf : (sep₁ ++ sep₂).isPrefixOf (sep₁ ++ l) := by
    rwa [← IsPrefix.iff_isPrefixOf, prefix_append_right_inj, IsPrefix.iff_isPrefixOf]
  conv => lhs; unfold splitOnList
  simp only [hnem, ↓reduceDite, length_append]
  rw [splitOnceRightP_of_P hpf]
  simp [drop_append_left]

theorem splitOnList_of_isPrefixOf {l sep : List α} (hsp : sep ≠ []) (hpf : sep.isPrefixOf l) :
    splitOnList l sep = [] :: splitOnList (l.drop sep.length) sep :=
  splitOnList_append_append_of_isPrefixOf [] hsp hpf

theorem splitOnList_refl_of_ne_nil (l : List α) (h : l ≠ []) : splitOnList l l = [[], []] := by
  have hpf : l.isPrefixOf l := IsPrefix.iff_isPrefixOf.mp (prefix_refl l)
  simp [splitOnList_of_isPrefixOf h hpf, splitOnList_nil_left]

theorem splitOnList_of_ne_nil_of_not_isPrefixOf {l sep : List α} (hne : l ≠ [])
    (hnpf : ¬sep.isPrefixOf l) :
    splitOnList l sep = modifyHead (l.head hne :: ·) (splitOnList l.tail sep) := by
  unfold splitOnList
  obtain ⟨a, sep, rfl⟩ := exists_cons_of_ne_nil (ne_nil_of_not_prefix (mt IsPrefix.iff_isPrefixOf.mp
    hnpf))
  simp only [isEmpty_cons, ↓reduceDite]
  rw [splitOnceRight_of_ne_nil_of_not_P hne hnpf]
  match splitOnceRightP (a::sep).isPrefixOf l.tail with
  | none => simp [head_cons_tail]
  | some (lf, rt) => rfl

theorem splitOnList_eq_singleton_of_length_lt {l sep : List α} (h : l.length < sep.length) :
    splitOnList l sep = [l] := by
  have hne : ¬sep.isEmpty := by
    simpa [isEmpty_iff_eq_nil, length_pos] using Nat.lt_of_le_of_lt (Nat.zero_le l.length) h
  unfold splitOnList
  simp only [hne, ↓reduceDite]
  rw [splitOnceRightP_isPrefixOf_eq_none_of_length_lt h]

end List

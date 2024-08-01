/-
Copyright (c) 2024 Bulhwi Cha, Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bulhwi Cha, Mario Carneiro
-/
import Batteries.Data.List.Lemmas
import Batteries.Data.List.NatLemmas
import Batteries.Tactic.SeqFocus

/-!
# `List.splitOnList`

This file introduces the `List.splitOnList` function, which is a specification for `String.splitOn`.
We need it to prove `String.splitOn_of_valid` in `Batteries.Data.String.Lemmas`.
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

theorem splitOnceRightP_isPrefixOf_eq_none_of_length_lt [BEq α] [LawfulBEq α] {l sep : List α}
    (h : l.length < sep.length) : splitOnceRightP sep.isPrefixOf l = none := by
  have not_isPrefixOf_of_length_lt {l} (h : l.length < sep.length) : ¬sep.isPrefixOf l := by
    simp [mt IsPrefix.length_le (Nat.not_le_of_lt h)]
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
[1, 1, 2, 3, 2, 4, 4].splitOnList []     = [[1, 1, 2, 3, 2, 4, 4]]
[1, 1, 2, 3, 2, 4, 4].splitOnList [5, 6] = [[1, 1, 2, 3, 2, 4, 4]]
[1, 1, 2, 3, 2, 4, 4].splitOnList [2, 3] = [[1, 1], [2, 4, 4]]
```
-/
def splitOnList [BEq α] [LawfulBEq α] (l sep : List α) : List (List α) :=
  if _h : sep.isEmpty then
    [l]
  else
    match _e : splitOnceRightP sep.isPrefixOf l with
    | none => [l]
    | some (l₁, l₂) => l₁ :: splitOnList (l₂.drop sep.length) sep
termination_by l.length
decreasing_by
  simp_wf
  rw [eq_append_of_splitOnceRightP l₁ l₂ _e, length_append]
  calc
    l₂.length - sep.length < l₂.length := Nat.sub_lt_self (by simp [length_pos,
      ← isEmpty_iff_eq_nil, _h]) (IsPrefix.length_le <| isPrefixOf_iff_IsPrefix.mp
      (P_of_splitOnceRightP l₁ l₂ _e))
    _ ≤ l₁.length + l₂.length := Nat.le_add_left ..

variable [BEq α] [LawfulBEq α]

theorem splitOnList_nil_left (sep : List α) : splitOnList [] sep = [[]] := by
  cases sep <;> unfold splitOnList <;> rfl

theorem splitOnList_nil_right (l : List α) : splitOnList l [] = [l] := by
  simp [splitOnList]

theorem splitOnList_append_append_of_isPrefixOf {l : List α} (sep₁) {sep₂} (hsp₂ : sep₂ ≠ [])
    (hpf : sep₂.isPrefixOf l) :
    splitOnList (sep₁ ++ l) (sep₁ ++ sep₂) =
      [] :: splitOnList (l.drop sep₂.length) (sep₁ ++ sep₂) := by
  have hnem : ¬(sep₁ ++ sep₂).isEmpty := by simp [isEmpty_iff_eq_nil, hsp₂]
  have hpf' : (sep₁ ++ sep₂).isPrefixOf (sep₁ ++ l) := by simpa [prefix_append_right_inj] using hpf
  conv => lhs; unfold splitOnList
  simp only [hnem, ↓reduceDite, length_append]
  rw [splitOnceRightP_of_P hpf']
  simp [drop_append_left]

theorem splitOnList_of_isPrefixOf {l sep : List α} (hsp : sep ≠ []) (hpf : sep.isPrefixOf l) :
    splitOnList l sep = [] :: splitOnList (l.drop sep.length) sep :=
  splitOnList_append_append_of_isPrefixOf [] hsp hpf

theorem splitOnList_refl_of_ne_nil (l : List α) (h : l ≠ []) : splitOnList l l = [[], []] := by
  have hpf : l.isPrefixOf l := isPrefixOf_iff_IsPrefix.mpr (prefix_refl l)
  simp [splitOnList_of_isPrefixOf h hpf, splitOnList_nil_left]

theorem splitOnList_of_ne_nil_of_not_isPrefixOf {l sep : List α} (hne : l ≠ [])
    (hnpf : ¬sep.isPrefixOf l) :
    splitOnList l sep = modifyHead (l.head hne :: ·) (splitOnList l.tail sep) := by
  unfold splitOnList
  obtain ⟨a, sep, rfl⟩ := exists_cons_of_ne_nil <| ne_nil_of_not_prefix <|
    mt isPrefixOf_iff_IsPrefix.mpr hnpf
  simp only [isEmpty_cons, ↓reduceDite]
  rw [splitOnceRight_of_ne_nil_of_not_P hne hnpf]
  match splitOnceRightP (a::sep).isPrefixOf l.tail with
  | none => simp [head_cons_tail]
  | some (lf, rt) => rfl

variable [DecidableEq α]

/-- An alternative definition of `splitOnList`. -/
theorem splitOnList_def (l sep : List α) :
    splitOnList l sep =
      if h : l = [] ∨ sep = [] then
        [l]
      else if sep.isPrefixOf l then
        [] :: splitOnList (l.drop sep.length) sep
      else
        modifyHead (l.head (not_or.mp h).1 :: ·) (splitOnList l.tail sep) := by
  split
  · next h =>
    match h with
    | .inl hls => rw [hls, splitOnList_nil_left]
    | .inr hsp => rw [hsp, splitOnList_nil_right]
  · next h =>
    let ⟨hls, hsp⟩ := not_or.mp h
    split <;> rename_i hpf
    · exact splitOnList_of_isPrefixOf hsp hpf
    · exact splitOnList_of_ne_nil_of_not_isPrefixOf hls hpf

theorem splitOnList_eq_singleton_of_length_lt {l sep : List α} (h : l.length < sep.length) :
    splitOnList l sep = [l] := by
  have hne : ¬sep.isEmpty := by
    simpa [isEmpty_iff_eq_nil, length_pos] using Nat.lt_of_le_of_lt (Nat.zero_le l.length) h
  unfold splitOnList
  simp only [hne, ↓reduceDite]
  rw [splitOnceRightP_isPrefixOf_eq_none_of_length_lt h]

/--
Auxiliary definition for proving `String.splitOnAux_of_valid`.

* `sep₁ ++ l`: the list with elements of the type `α` that `splitOnListAux` will split.
* `sep₁ ++ sep₂`: the separator. The list will be split on occurrences of this.
* `sep₁`: the common prefix of the list and the separator.
* `l`: the latter part of the list.
* `sep₂`: the latter part of the separator.
-/
def splitOnListAux (l sep₁ sep₂ : List α) (h : sep₂ ≠ []) : List (List α) :=
  if hls : l = [] then
    [sep₁]
  else
    if l.head hls = sep₂.head h then
      if htl₂ : sep₂.tail = [] then
        [] :: splitOnListAux l.tail [] (sep₁ ++ [sep₂.head h]) (by simp)
      else
        splitOnListAux l.tail (sep₁ ++ [l.head hls]) sep₂.tail htl₂
    else
      modifyHead ((sep₁ ++ l).head (by simp [hls]) :: ·) <| splitOnListAux (sep₁ ++ l).tail []
        (sep₁ ++ sep₂) (by simp [h])
termination_by (sep₁.length + l.length, sep₂.length)
decreasing_by
  all_goals simp_wf
  · left; calc
      l.length - 1 < l.length := Nat.pred_lt (mt length_eq_zero.mp hls)
      _ ≤ sep₁.length + l.length := Nat.le_add_left ..
  · have heq : sep₁.length + 1 + (l.length - 1) = sep₁.length + l.length := by
      rw [← Nat.add_sub_assoc (show 1 ≤ l.length from length_pos.mpr hls), Nat.add_right_comm,
        Nat.add_sub_cancel]
    rw [heq]; clear heq
    right
    exact Nat.pred_lt (mt length_eq_zero.mp h)
  · left
    apply Nat.pred_lt; show ¬length sep₁ + length l = 0
    rw [Nat.add_eq_zero_iff, length_eq_zero (l := l)]
    exact not_and_of_not_right _ hls

theorem splitOnListAux_eq_splitOnList_append_append (l sep₁ sep₂ : List α) (h : sep₂ ≠ []) :
    splitOnListAux l sep₁ sep₂ h = splitOnList (sep₁ ++ l) (sep₁ ++ sep₂) := by
  rw [splitOnListAux]
  split
  · next hls =>
    simp only [hls, append_nil]
    rw [splitOnList_eq_singleton_of_length_lt]
    exact IsPrefix.length_lt_of_ne (prefix_append ..) (Ne.symm <| mt append_right_eq_self.mp h)
  · next hls =>
    split
    · next hhd =>
      split
      · next htl₂ =>
        conv => rhs; rw [← head_cons_tail sep₂ h, htl₂]
        have hpf : (sep₁ ++ [sep₂.head h]).isPrefixOf (sep₁ ++ l) := by
          rw [← head_cons_tail l hls, hhd, isPrefixOf_iff_IsPrefix, append_cons _ _ l.tail]
          apply prefix_append
        have hdr : (sep₁ ++ [sep₂.head h] ++ l.tail).drop (sep₁ ++ [sep₂.head h]).length = l.tail :=
          drop_append 0
        simp only [splitOnList_of_isPrefixOf (by simp) hpf, cons.injEq, true_and]
        conv => rhs; arg 1; arg 2; rw [← head_cons_tail l hls, hhd, append_cons]
        rw [hdr]
        exact splitOnListAux_eq_splitOnList_append_append l.tail [] (sep₁++[sep₂.head h]) (by simp)
      · next htl₂ =>
        have ih := splitOnListAux_eq_splitOnList_append_append l.tail (sep₁++[l.head hls]) sep₂.tail
          htl₂
        simp only [append_assoc, singleton_append, head_cons_tail] at ih
        conv at ih => rhs; arg 2; rw [hhd, head_cons_tail]
        exact ih
    · next hhd =>
      have hnpf : ¬isPrefixOf (sep₁ ++ sep₂) (sep₁ ++ l) := by
        rw [isPrefixOf_iff_IsPrefix, prefix_append_right_inj, prefix_iff_head_eq_and_tail_prefix h
          hls]
        exact not_and_of_not_left _ (Ne.symm hhd)
      rw [splitOnList_of_ne_nil_of_not_isPrefixOf (by simp [hls]) hnpf]
      apply congrArg
      exact splitOnListAux_eq_splitOnList_append_append (sep₁++l).tail [] (sep₁++sep₂) (by simp [h])
termination_by (sep₁.length + l.length, sep₂.length)
decreasing_by
  all_goals simp_wf
  · rename_i _₀ _₁ _₂ _₃ _₄ _₅ hls _hhd; clear _₀ _₁ _₂ _₃ _₄ _₅
    left
    rw [Nat.add_sub_assoc (show 1 ≤ l.length from length_pos.mpr hls), Nat.add_lt_add_iff_left]
    exact Nat.pred_lt (mt length_eq_zero.mp hls)
  · rename_i _₀ _₁ _₂ _₃ _₄ _₅ hls _hhd _htl₂; clear _₀ _₁ _₂ _₃ _₄ _₅
    have heq : sep₁.length + 1 + (l.length - 1) = sep₁.length + l.length := by
      rw [← Nat.add_sub_assoc (show 1 ≤ l.length from length_pos.mpr hls), Nat.add_right_comm,
        Nat.add_sub_cancel]
    rw [heq]; clear heq
    right
    exact Nat.pred_lt (mt length_eq_zero.mp h)
  · rename_i _₀ _₁ _₂ _₃ _₄ _₅ hls _hhd _htl₂; clear _₀ _₁ _₂ _₃ _₄ _₅
    left
    calc
      l.length - 1 < l.length := Nat.pred_lt (mt length_eq_zero.mp hls)
      l.length ≤ sep₁.length + l.length := Nat.le_add_left ..

end List

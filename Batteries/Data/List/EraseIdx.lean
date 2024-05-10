/-
Copyright (c) 2024 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Batteries.Data.List.Lemmas

/-!
# Basic properties of `List.eraseIdx`

`List.eraseIdx l k` erases `k`-th element of `l : List α`.
If `k ≥ length l`, then it returns `l`.
-/

namespace List

universe u v
variable {α : Type u} {β : Type v}

@[simp] theorem eraseIdx_zero (l : List α) : eraseIdx l 0 = tail l := by cases l <;> rfl

theorem eraseIdx_eq_take_drop_succ :
    ∀ (l : List α) (i : Nat), l.eraseIdx i = l.take i ++ l.drop (i + 1)
  | nil, _ => by simp
  | a::l, 0 => by simp
  | a::l, i + 1 => by simp [eraseIdx_eq_take_drop_succ l i]

theorem eraseIdx_sublist : ∀ (l : List α) (k : Nat), eraseIdx l k <+ l
  | [], _ => by simp
  | a::l, 0 => by simp
  | a::l, k + 1 => by simp [eraseIdx_sublist l k]

theorem eraseIdx_subset (l : List α) (k : Nat) : eraseIdx l k ⊆ l := (eraseIdx_sublist l k).subset

@[simp]
theorem eraseIdx_eq_self : ∀ {l : List α} {k : Nat}, eraseIdx l k = l ↔ length l ≤ k
  | [], _ => by simp
  | a::l, 0 => by simp [(cons_ne_self _ _).symm]
  | a::l, k + 1 => by simp [eraseIdx_eq_self]

alias ⟨_, eraseIdx_of_length_le⟩ := eraseIdx_eq_self

theorem eraseIdx_append_of_lt_length {l : List α} {k : Nat} (hk : k < length l) (l' : List α) :
    eraseIdx (l ++ l') k = eraseIdx l k ++ l' := by
  rw [eraseIdx_eq_take_drop_succ, take_append_of_le_length, drop_append_of_le_length,
    eraseIdx_eq_take_drop_succ, append_assoc]
  all_goals omega

theorem eraseIdx_append_of_length_le {l : List α} {k : Nat} (hk : length l ≤ k) (l' : List α) :
    eraseIdx (l ++ l') k = l ++ eraseIdx l' (k - length l) := by
  rw [eraseIdx_eq_take_drop_succ, eraseIdx_eq_take_drop_succ,
    take_append_eq_append_take, drop_append_eq_append_drop,
    take_all_of_le hk, drop_eq_nil_of_le (by omega), nil_append, append_assoc]
  congr
  omega

protected theorem IsPrefix.eraseIdx {l l' : List α} (h : l <+: l') (k : Nat) :
    eraseIdx l k <+: eraseIdx l' k := by
  rcases h with ⟨t, rfl⟩
  if hkl : k < length l then
    simp [eraseIdx_append_of_lt_length hkl]
  else
    rw [Nat.not_lt] at hkl
    simp [eraseIdx_append_of_length_le hkl, eraseIdx_of_length_le hkl]

theorem mem_eraseIdx_iff_get {x : α} :
    ∀ {l} {k}, x ∈ eraseIdx l k ↔ ∃ i : Fin l.length, ↑i ≠ k ∧ l.get i = x
  | [], _ => by
    simp only [eraseIdx, Fin.exists_iff, not_mem_nil, false_iff]
    rintro ⟨i, h, -⟩
    exact Nat.not_lt_zero _ h
  | a::l, 0 => by simp [Fin.exists_fin_succ, mem_iff_get]
  | a::l, k+1 => by
    simp [Fin.exists_fin_succ, mem_eraseIdx_iff_get, @eq_comm _ a, k.succ_ne_zero.symm]

theorem mem_eraseIdx_iff_get? {x : α} {l} {k} : x ∈ eraseIdx l k ↔ ∃ i ≠ k, l.get? i = x := by
  simp only [mem_eraseIdx_iff_get, Fin.exists_iff, exists_and_left, get_eq_iff, exists_prop]
  refine exists_congr fun i ↦ and_congr_right' <| and_iff_right_of_imp fun h ↦ ?_
  obtain ⟨h, -⟩ := get?_eq_some.1 h
  exact h

end List

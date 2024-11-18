/-
Copyright (c) 2021 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Mario Carneiro, Gabriel Ebner
-/
import Batteries.Data.List.Lemmas
import Batteries.Data.Array.Basic
import Batteries.Tactic.SeqFocus
import Batteries.Util.ProofWanted

namespace Array

theorem forIn_eq_forIn_toList [Monad m]
    (as : Array α) (b : β) (f : α → β → m (ForInStep β)) :
    forIn as b f = forIn as.toList b f := by
  cases as
  simp

@[deprecated (since := "2024-09-09")] alias forIn_eq_forIn_data := forIn_eq_forIn_toList
@[deprecated (since := "2024-08-13")] alias forIn_eq_data_forIn := forIn_eq_forIn_data

/-! ### zipWith / zip -/

@[deprecated (since := "2024-09-09")] alias data_zipWith := toList_zipWith
@[deprecated (since := "2024-08-13")] alias zipWith_eq_zipWith_data := data_zipWith

@[simp] theorem size_zipWith (as : Array α) (bs : Array β) (f : α → β → γ) :
    (as.zipWith bs f).size = min as.size bs.size := by
  rw [size_eq_length_toList, toList_zipWith, List.length_zipWith]

@[simp] theorem size_zip (as : Array α) (bs : Array β) :
    (as.zip bs).size = min as.size bs.size :=
  as.size_zipWith bs Prod.mk

/-! ### filter -/

theorem size_filter_le (p : α → Bool) (l : Array α) :
    (l.filter p).size ≤ l.size := by
  simp only [← length_toList, toList_filter]
  apply List.length_filter_le

/-! ### flatten -/

@[deprecated (since := "2024-09-09")] alias data_join := toList_flatten
@[deprecated (since := "2024-08-13")] alias join_data := toList_flatten
@[deprecated (since := "2024-10-15")] alias mem_join := mem_flatten

/-! ### indexOf? -/

theorem indexOf?_toList [BEq α] {a : α} {l : Array α} :
    l.toList.indexOf? a = (l.indexOf? a).map Fin.val := by
  simpa using aux l 0
where
  aux (l : Array α) (i : Nat) :
       ((l.toList.drop i).indexOf? a).map (·+i) = (indexOfAux l a i).map Fin.val := by
    rw [indexOfAux]
    if h : i < l.size then
      rw [List.drop_eq_getElem_cons h, ←getElem_eq_getElem_toList, List.indexOf?_cons]
      if h' : l[i] == a then
        simp [h, h']
      else
        simp [h, h', ←aux l (i+1), Function.comp_def, ←Nat.add_assoc, Nat.add_right_comm]
    else
      have h' : l.size ≤ i := Nat.le_of_not_lt h
      simp [h, List.drop_of_length_le h', List.indexOf?]
  termination_by l.size - i

/-! ### erase -/

@[simp] proof_wanted toList_erase [BEq α] {l : Array α} {a : α} :
    (l.erase a).toList = l.toList.erase a

@[simp] theorem eraseIdx!_eq_eraseIdx (a : Array α) (i : Nat) :
    a.eraseIdx! i = a.eraseIdx i := rfl

@[simp] theorem size_eraseIdx (a : Array α) (i : Nat) :
    (a.eraseIdx i).size = if i < a.size then a.size-1 else a.size := by
  simp only [eraseIdx]; split; simp; rfl

/-! ### set -/

theorem size_set! (a : Array α) (i v) : (a.set! i v).size = a.size := by simp

/-! ### map -/

theorem mapM_empty [Monad m] (f : α → m β) : mapM f #[] = pure #[] := by
  rw [mapM, mapM.map]; rfl

theorem map_empty (f : α → β) : map f #[] = #[] := mapM_empty f

/-! ### mem -/

theorem mem_singleton : a ∈ #[b] ↔ a = b := by simp

/-! ### append -/

alias append_empty := append_nil

alias empty_append := nil_append

/-! ### insertAt -/

private theorem size_insertAt_loop (as : Array α) (i : Fin (as.size+1)) (j : Fin bs.size) :
    (insertAt.loop as i bs j).size = bs.size := by
  unfold insertAt.loop
  split
  · rw [size_insertAt_loop, size_swap]
  · rfl

@[simp] theorem size_insertAt (as : Array α) (i : Fin (as.size+1)) (v : α) :
    (as.insertAt i v).size = as.size + 1 := by
  rw [insertAt, size_insertAt_loop, size_push]

private theorem get_insertAt_loop_lt (as : Array α) (i : Fin (as.size+1)) (j : Fin bs.size)
    (k) (hk : k < (insertAt.loop as i bs j).size) (h : k < i) :
    (insertAt.loop as i bs j)[k] = bs[k]'(size_insertAt_loop .. ▸ hk) := by
  unfold insertAt.loop
  split
  · have h1 : k ≠ j - 1 := by omega
    have h2 : k ≠ j := by omega
    rw [get_insertAt_loop_lt, getElem_swap, if_neg h1, if_neg h2]
    exact h
  · rfl

private theorem get_insertAt_loop_gt (as : Array α) (i : Fin (as.size+1)) (j : Fin bs.size)
    (k) (hk : k < (insertAt.loop as i bs j).size) (hgt : j < k) :
    (insertAt.loop as i bs j)[k] = bs[k]'(size_insertAt_loop .. ▸ hk) := by
  unfold insertAt.loop
  split
  · have h1 : k ≠ j - 1 := by omega
    have h2 : k ≠ j := by omega
    rw [get_insertAt_loop_gt, getElem_swap, if_neg h1, if_neg h2]
    exact Nat.lt_of_le_of_lt (Nat.pred_le _) hgt
  · rfl

private theorem get_insertAt_loop_eq (as : Array α) (i : Fin (as.size+1)) (j : Fin bs.size)
    (k) (hk : k < (insertAt.loop as i bs j).size) (heq : i = k) (h : i.val ≤ j.val) :
    (insertAt.loop as i bs j)[k] = bs[j] := by
  unfold insertAt.loop
  split
  · next h =>
    rw [get_insertAt_loop_eq, Fin.getElem_fin, getElem_swap, if_pos rfl]
    exact heq
    exact Nat.le_pred_of_lt h
  · congr; omega

private theorem get_insertAt_loop_gt_le (as : Array α) (i : Fin (as.size+1)) (j : Fin bs.size)
    (k) (hk : k < (insertAt.loop as i bs j).size) (hgt : i < k) (hle : k ≤ j) :
    (insertAt.loop as i bs j)[k] = bs[k-1] := by
  unfold insertAt.loop
  split
  · next h =>
    if h0 : k = j then
      cases h0
      have h1 : j.val ≠ j - 1 := by omega
      rw [get_insertAt_loop_gt, getElem_swap, if_neg h1, if_pos rfl]; rfl
      exact Nat.pred_lt_of_lt hgt
    else
      have h1 : k - 1 ≠ j - 1 := by omega
      have h2 : k - 1 ≠ j := by omega
      rw [get_insertAt_loop_gt_le, getElem_swap, if_neg h1, if_neg h2]
      apply Nat.le_of_lt_add_one
      rw [Nat.sub_one_add_one]
      exact Nat.lt_of_le_of_ne hle h0
      exact Nat.not_eq_zero_of_lt h
      exact hgt
  · next h =>
    absurd h
    exact Nat.lt_of_lt_of_le hgt hle

theorem getElem_insertAt_lt (as : Array α) (i : Fin (as.size+1)) (v : α)
    (k) (hlt : k < i.val) {hk : k < (as.insertAt i v).size} {hk' : k < as.size} :
    (as.insertAt i v)[k] = as[k] := by
  simp only [insertAt]
  rw [get_insertAt_loop_lt, getElem_push, dif_pos hk']
  exact hlt

theorem getElem_insertAt_gt (as : Array α) (i : Fin (as.size+1)) (v : α)
    (k) (hgt : k > i.val) {hk : k < (as.insertAt i v).size} {hk' : k - 1 < as.size} :
    (as.insertAt i v)[k] = as[k - 1] := by
  simp only [insertAt]
  rw [get_insertAt_loop_gt_le, getElem_push, dif_pos hk']
  exact hgt
  rw [size_insertAt] at hk
  exact Nat.le_of_lt_succ hk

theorem getElem_insertAt_eq (as : Array α) (i : Fin (as.size+1)) (v : α)
    (k) (heq : i.val = k) {hk : k < (as.insertAt i v).size} :
    (as.insertAt i v)[k] = v := by
  simp only [insertAt]
  rw [get_insertAt_loop_eq, Fin.getElem_fin, getElem_push_eq]
  exact heq
  exact Nat.le_of_lt_succ i.is_lt

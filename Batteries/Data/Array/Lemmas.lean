/-
Copyright (c) 2021 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Mario Carneiro, Gabriel Ebner
-/
import Batteries.Data.List.Lemmas
import Batteries.Data.List.FinRange
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

theorem toList_zipWith (f : α → β → γ) (as : Array α) (bs : Array β) :
    (as.zipWith bs f).toList = as.toList.zipWith f bs.toList := by
  let rec loop : ∀ (i : Nat) cs, i ≤ as.size → i ≤ bs.size →
      (zipWithAux f as bs i cs).toList =
        cs.toList ++ (as.toList.drop i).zipWith f (bs.toList.drop i) := by
    intro i cs hia hib
    unfold zipWithAux
    by_cases h : i = as.size ∨ i = bs.size
    case pos =>
      have : ¬(i < as.size) ∨ ¬(i < bs.size) := by
        cases h <;> simp_all only [Nat.not_lt, Nat.le_refl, true_or, or_true]
      -- Cleaned up aesop output below
      simp_all only [Nat.not_lt]
      cases h <;> [(cases this); (cases this)]
      · simp_all only [Nat.le_refl, Nat.lt_irrefl, dite_false, List.drop_length,
                      List.zipWith_nil_left, List.append_nil]
      · simp_all only [Nat.le_refl, Nat.lt_irrefl, dite_false, List.drop_length,
                      List.zipWith_nil_left, List.append_nil]
      · simp_all only [Nat.le_refl, Nat.lt_irrefl, dite_false, List.drop_length,
                      List.zipWith_nil_right, List.append_nil]
        split <;> simp_all only [Nat.not_lt]
      · simp_all only [Nat.le_refl, Nat.lt_irrefl, dite_false, List.drop_length,
                      List.zipWith_nil_right, List.append_nil]
        split <;> simp_all only [Nat.not_lt]
    case neg =>
      rw [not_or] at h
      have has : i < as.size := Nat.lt_of_le_of_ne hia h.1
      have hbs : i < bs.size := Nat.lt_of_le_of_ne hib h.2
      simp only [has, hbs, dite_true]
      rw [loop (i+1) _ has hbs, Array.push_toList]
      have h₁ : [f as[i] bs[i]] = List.zipWith f [as[i]] [bs[i]] := rfl
      let i_as : Fin as.toList.length := ⟨i, has⟩
      let i_bs : Fin bs.toList.length := ⟨i, hbs⟩
      rw [h₁, List.append_assoc]
      congr
      rw [← List.zipWith_append (h := by simp), getElem_eq_getElem_toList,
        getElem_eq_getElem_toList]
      show List.zipWith f (as.toList[i_as] :: List.drop (i_as + 1) as.toList)
        ((List.get bs.toList i_bs) :: List.drop (i_bs + 1) bs.toList) =
        List.zipWith f (List.drop i as.toList) (List.drop i bs.toList)
      simp only [length_toList, Fin.getElem_fin, List.getElem_cons_drop, List.get_eq_getElem]
  simp [zipWith, loop 0 #[] (by simp) (by simp)]
@[deprecated (since := "2024-09-09")] alias data_zipWith := toList_zipWith
@[deprecated (since := "2024-08-13")] alias zipWith_eq_zipWith_data := data_zipWith

@[simp] theorem size_zipWith (as : Array α) (bs : Array β) (f : α → β → γ) :
    (as.zipWith bs f).size = min as.size bs.size := by
  rw [size_eq_length_toList, toList_zipWith, List.length_zipWith]

theorem toList_zip (as : Array α) (bs : Array β) :
    (as.zip bs).toList = as.toList.zip bs.toList :=
  toList_zipWith Prod.mk as bs
@[deprecated (since := "2024-09-09")] alias data_zip := toList_zip
@[deprecated (since := "2024-08-13")] alias zip_eq_zip_data := data_zip

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

/-! ### ofFn -/

@[simp] theorem toList_ofFn (f : Fin n → α) : (ofFn f).toList = List.ofFn f := by
  apply List.ext_getElem <;> simp

/-! ### finRange -/

@[simp] theorem size_finRange (n) : (Array.finRange n).size = n := by
  simp [Array.finRange]

@[simp] theorem getElem_finRange (n i) (h : i < (Array.finRange n).size) :
    (Array.finRange n)[i] = ⟨i, size_finRange n ▸ h⟩ := by
  simp [Array.finRange]

@[simp] theorem toList_finRange (n) : (Array.finRange n).toList = List.finRange n := by
  simp [Array.finRange, List.finRange]

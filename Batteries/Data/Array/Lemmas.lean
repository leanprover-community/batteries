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

@[deprecated (since := "2024-09-09")] alias data_zipWith := toList_zipWith
@[deprecated (since := "2024-08-13")] alias zipWith_eq_zipWith_data := data_zipWith

/-! ### flatten -/

@[deprecated (since := "2024-09-09")] alias data_join := toList_flatten
@[deprecated (since := "2024-08-13")] alias join_data := toList_flatten
@[deprecated (since := "2024-10-15")] alias mem_join := mem_flatten

end Array

/-! ### indexOf? -/

namespace Array

theorem findIdx?_loop_eq_map_findFinIdx?_loop_val {xs : Array α} {p : α → Bool} {j} :
    findIdx?.loop p xs j = (findFinIdx?.loop p xs j).map (·.val) := by
  unfold findIdx?.loop
  unfold findFinIdx?.loop
  split <;> rename_i h
  case isTrue =>
    split
    case isTrue => simp
    case isFalse =>
      have : xs.size - (j + 1) < xs.size - j := Nat.sub_succ_lt_self xs.size j h
      rw [findIdx?_loop_eq_map_findFinIdx?_loop_val (j := j + 1)]
  case isFalse => simp
termination_by xs.size - j

theorem findIdx?_eq_map_findFinIdx?_val {xs : Array α} {p : α → Bool} :
    xs.findIdx? p = (xs.findFinIdx? p).map (·.val) := by
  simp [findIdx?, findFinIdx?, findIdx?_loop_eq_map_findFinIdx?_loop_val]

end Array

namespace List

theorem findFinIdx?_go_beq_eq_idxOfAux_toArray [BEq α]
    {xs as : List α} {a : α} {i : Nat} {h} (w : as = xs.drop i) :
    findFinIdx?.go (fun x => x == a) xs as i h =
      xs.toArray.idxOfAux a i := by
  unfold findFinIdx?.go
  unfold Array.idxOfAux
  split <;> rename_i b as
  · simp at h
    simp [h]
  · simp at h
    rw [dif_pos (by simp; omega)]
    simp only [getElem_toArray]
    erw [getElem_drop' (j := 0)]
    simp only [← w, getElem_cons_zero]
    have : xs.length - (i + 1) < xs.length - i := by omega
    rw [findFinIdx?_go_beq_eq_idxOfAux_toArray]
    rw [← drop_drop, ← w]
    simp
termination_by xs.length - i

@[simp] theorem finIdxOf?_toArray [BEq α] {as : List α} {a : α} :
    as.toArray.finIdxOf? a = as.finIdxOf? a := by
  unfold Array.finIdxOf?
  unfold finIdxOf?
  unfold findFinIdx?
  rw [findFinIdx?_go_beq_eq_idxOfAux_toArray]
  simp

theorem findIdx?_go_eq_map_findFinIdx?_go_val {xs : List α} {p : α → Bool} {i : Nat} {h} :
    List.findIdx?.go p xs i =
      (List.findFinIdx?.go p l xs i h).map (·.val) := by
  unfold findIdx?.go
  unfold findFinIdx?.go
  split <;> rename_i a xs
  · simp_all
  · simp only
    split
    · simp
    · rw [findIdx?_go_eq_map_findFinIdx?_go_val]

theorem findIdx?_eq_map_findFinIdx?_val {xs : List α} {p : α → Bool} :
    xs.findIdx? p = (xs.findFinIdx? p).map (·.val) := by
  simp [findIdx?, findFinIdx?]
  rw [findIdx?_go_eq_map_findFinIdx?_go_val]

theorem idxOf?_eq_map_finIdxOf?_val [BEq α] {xs : List α} {a : α} :
    xs.idxOf? a = (xs.finIdxOf? a).map (·.val) := by
  simp [idxOf?, finIdxOf?, findIdx?_eq_map_findFinIdx?_val]

@[simp] theorem idxOf?_toArray [BEq α] {as : List α} {a : α} :
    as.toArray.idxOf? a = as.idxOf? a := by
  rw [Array.idxOf?, finIdxOf?_toArray, idxOf?_eq_map_finIdxOf?_val]

open Array in
@[simp] theorem findIdx?_toArray {as : List α} {p : α → Bool} :
    as.toArray.findIdx? p = as.findIdx? p := by
  unfold Array.findIdx?
  suffices ∀ i, i ≤ as.length →
      Array.findIdx?.loop p as.toArray (as.length - i) =
        (findIdx? p (as.drop  (as.length - i))).map fun j => j +  (as.length - i) by
    specialize this as.length
    simpa
  intro i
  induction i with
  | zero => simp [findIdx?.loop]
  | succ i ih =>
    unfold findIdx?.loop
    simp only [size_toArray, getElem_toArray]
    split <;> rename_i h
    · rw [drop_eq_getElem_cons h]
      rw [findIdx?_cons]
      split <;> rename_i h'
      · simp
      · intro w
        have : as.length - (i + 1) + 1 = as.length - i := by omega
        specialize ih (by omega)
        simp only [Option.map_map, this, ih]
        congr
        ext
        simp
        omega
    · have : as.length = 0 := by omega
      simp_all

@[simp] theorem findFinIdx?_toArray {as : List α} {p : α → Bool} :
    as.toArray.findFinIdx? p = as.findFinIdx? p := by
  have h := findIdx?_toArray (as := as) (p := p)
  rw [findIdx?_eq_map_findFinIdx?_val, Array.findIdx?_eq_map_findFinIdx?_val] at h
  rwa [Option.map_inj_right] at h
  rintro ⟨x, hx⟩ ⟨y, hy⟩ rfl
  simp

end List

open List

namespace Array

theorem idxOf?_toList [BEq α] {a : α} {l : Array α} :
    l.toList.idxOf? a = l.idxOf? a := by
  rcases l with ⟨l⟩
  simp

/-! ### erase -/

@[simp] theorem eraseP_toArray {as : List α} {p : α → Bool} :
    as.toArray.eraseP p = (as.eraseP p).toArray := by
  rw [Array.eraseP, List.eraseP_eq_eraseIdx, findFinIdx?_toArray]
  split
  · simp only [List.findIdx?_eq_map_findFinIdx?_val, Option.map_none', *]
  · simp only [eraseIdx_toArray, List.findIdx?_eq_map_findFinIdx?_val, Option.map_some', *]

-- Adaptation note: We can remove the `LawfulBEq α` assumption again on nightly-2025-01-31.
@[simp] theorem erase_toArray [BEq α] [LawfulBEq α] {as : List α} {a : α} :
    as.toArray.erase a = (as.erase a).toArray := by
  rw [Array.erase, finIdxOf?_toArray, List.erase_eq_eraseIdx]
  rw [idxOf?_eq_map_finIdxOf?_val]
  split <;> simp_all

-- Adaptation note: We can remove the `LawfulBEq α` assumption again on nightly-2025-01-31.
@[simp] theorem toList_erase [BEq α] [LawfulBEq α] (l : Array α) (a : α) :
    (l.erase a).toList = l.toList.erase a := by
  rcases l with ⟨l⟩
  simp

@[simp] theorem size_eraseIdxIfInBounds (a : Array α) (i : Nat) :
    (a.eraseIdxIfInBounds i).size = if i < a.size then a.size-1 else a.size := by
  simp only [eraseIdxIfInBounds]; split; simp; rfl

/-! ### set -/

theorem size_set! (a : Array α) (i v) : (a.set! i v).size = a.size := by simp

/-! ### map -/

/-! ### mem -/

/-! ### insertAt -/

@[simp] private theorem size_insertIdx_loop (as : Array α) (i : Nat) (j : Fin as.size) :
    (insertIdx.loop i as j).size = as.size := by
  unfold insertIdx.loop
  split
  · rw [size_insertIdx_loop, size_swap]
  · rfl

@[simp] theorem size_insertIdx (as : Array α) (i : Nat) (h : i ≤ as.size) (v : α) :
    (as.insertIdx i v).size = as.size + 1 := by
  rw [insertIdx, size_insertIdx_loop, size_push]

@[deprecated size_insertIdx (since := "2024-11-20")] alias size_insertAt := size_insertIdx

theorem getElem_insertIdx_loop_lt {as : Array α} {i : Nat} {j : Fin as.size} {k : Nat} {h}
    (w : k < i) :
    (insertIdx.loop i as j)[k] = as[k]'(by simpa using h) := by
  unfold insertIdx.loop
  split <;> rename_i h₁
  · simp only
    rw [getElem_insertIdx_loop_lt w]
    rw [getElem_swap]
    split <;> rename_i h₂
    · simp_all
      omega
    · split <;> rename_i h₃
      · omega
      · simp_all
  · rfl

theorem getElem_insertIdx_loop_eq {as : Array α} {i : Nat} {j : Nat} {hj : j < as.size} {h} :
    (insertIdx.loop i as ⟨j, hj⟩)[i] = if i ≤ j then as[j] else as[i]'(by simpa using h) := by
  unfold insertIdx.loop
  split <;> rename_i h₁
  · simp at h₁
    have : j - 1 < j := by omega
    rw [getElem_insertIdx_loop_eq]
    rw [getElem_swap]
    simp
    split <;> rename_i h₂
    · rw [if_pos (by omega)]
    · omega
  · simp at h₁
    by_cases h' : i = j
    · simp [h']
    · have t : ¬ i ≤ j := by omega
      simp [t]

theorem getElem_insertIdx_loop_gt {as : Array α} {i : Nat} {j : Nat} {hj : j < as.size}
    {k : Nat} {h} (w : i < k) :
    (insertIdx.loop i as ⟨j, hj⟩)[k] =
      if k ≤ j then as[k-1]'(by simp at h; omega) else as[k]'(by simpa using h) := by
  unfold insertIdx.loop
  split <;> rename_i h₁
  · simp only
    simp only at h₁
    have : j - 1 < j := by omega
    rw [getElem_insertIdx_loop_gt w]
    rw [getElem_swap]
    split <;> rename_i h₂
    · rw [if_neg (by omega), if_neg (by omega)]
      have t : k ≤ j := by omega
      simp [t]
    · rw [getElem_swap]
      rw [if_neg (by omega)]
      split <;> rename_i h₃
      · simp [h₃]
      · have t : ¬ k ≤ j := by omega
        simp [t]
  · simp only at h₁
    have t : ¬ k ≤ j := by omega
    simp [t]

theorem getElem_insertIdx_loop {as : Array α} {i : Nat} {j : Nat} {hj : j < as.size} {k : Nat} {h} :
    (insertIdx.loop i as ⟨j, hj⟩)[k] =
      if h₁ : k < i then
        as[k]'(by simpa using h)
      else
        if h₂ : k = i then
          if i ≤ j then as[j] else as[i]'(by simpa [h₂] using h)
        else
          if k ≤ j then as[k-1]'(by simp at h; omega) else as[k]'(by simpa using h) := by
  split <;> rename_i h₁
  · rw [getElem_insertIdx_loop_lt h₁]
  · split <;> rename_i h₂
    · subst h₂
      rw [getElem_insertIdx_loop_eq]
    · rw [getElem_insertIdx_loop_gt (by omega)]

theorem getElem_insertIdx (as : Array α) (i : Nat) (h : i ≤ as.size) (v : α)
    (k) (h' : k < (as.insertIdx i v).size) :
    (as.insertIdx i v)[k] =
      if h₁ : k < i then
        as[k]'(by omega)
      else
        if h₂ : k = i then
          v
        else
          as[k - 1]'(by simp at h'; omega) := by
  unfold insertIdx
  rw [getElem_insertIdx_loop]
  simp only [size_insertIdx] at h'
  replace h' : k ≤ as.size := by omega
  simp only [getElem_push, h, ↓reduceIte, Nat.lt_irrefl, ↓reduceDIte, h', dite_eq_ite]
  split <;> rename_i h₁
  · rw [dif_pos (by omega)]
  · split <;> rename_i h₂
    · simp [h₂]
    · split <;> rename_i h₃
      · rfl
      · omega

theorem getElem_insertIdx_lt (as : Array α) (i : Nat) (h : i ≤ as.size) (v : α)
    (k) (h' : k < (as.insertIdx i v).size) (h : k < i) :
    (as.insertIdx i v)[k] = as[k] := by
  simp [getElem_insertIdx, h]

@[deprecated getElem_insertIdx_lt (since := "2024-11-20")] alias getElem_insertAt_lt :=
getElem_insertIdx_lt

theorem getElem_insertIdx_eq (as : Array α) (i : Nat) (h : i ≤ as.size) (v : α) :
    (as.insertIdx i v)[i]'(by simp; omega) = v := by
  simp [getElem_insertIdx, h]

@[deprecated getElem_insertIdx_eq (since := "2024-11-20")] alias getElem_insertAt_eq :=
getElem_insertIdx_eq

theorem getElem_insertIdx_gt (as : Array α) (i : Nat) (h : i ≤ as.size) (v : α)
    (k) (h' : k < (as.insertIdx i v).size) (h : i < k) :
    (as.insertIdx i v)[k] = as[k-1]'(by simp at h'; omega) := by
  rw [getElem_insertIdx]
  rw [dif_neg (by omega), dif_neg (by omega)]

@[deprecated getElem_insertIdx_gt (since := "2024-11-20")] alias getElem_insertAt_gt :=
getElem_insertIdx_gt

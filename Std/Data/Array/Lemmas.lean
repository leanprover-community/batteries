/-
Copyright (c) 2021 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Mario Carneiro, Gabriel Ebner
-/
import Std.Data.Nat.Lemmas
import Std.Data.List.Lemmas
import Std.Tactic.HaveI
import Std.Tactic.Simpa

local macro_rules | `($x[$i]'$h) => `(getElem $x $i $h)

@[simp] theorem getElem_fin [GetElem Cont Nat Elem Dom] (a : Cont) (i : Fin n) (h : Dom a i) :
    a[i] = a[i.1] := rfl

@[simp] theorem getElem?_fin [GetElem Cont Nat Elem Dom] (a : Cont) (i : Fin n)
    [Decidable (Dom a i)] : a[i]? = a[i.1]? := rfl

@[simp] theorem getElem!_fin [GetElem Cont Nat Elem Dom] (a : Cont) (i : Fin n)
    [Decidable (Dom a i)] [Inhabited Elem] : a[i]! = a[i.1]! := rfl

theorem getElem?_pos [GetElem Cont Idx Elem Dom]
    (a : Cont) (i : Idx) (h : Dom a i) [Decidable (Dom a i)] : a[i]? = a[i] := dif_pos h

theorem getElem?_neg [GetElem Cont Idx Elem Dom]
    (a : Cont) (i : Idx) (h : ¬Dom a i) [Decidable (Dom a i)] : a[i]? = none := dif_neg h

namespace Array

@[simp] theorem toArray_data : (a : Array α) → a.data.toArray = a
  | ⟨l⟩ => ext' (data_toArray l)

@[simp] theorem get_eq_getElem (a : Array α) (i : Nat) (h) : a.get ⟨i, h⟩ = a[i] := rfl
@[simp] theorem getElem_fin_eq_getElem (a : Array α) (i : Fin a.size) : a[i] = a[i.1] := rfl
@[simp] theorem getElem?_fin_eq_get? (a : Array α) (i : Fin a.size) : a[i]? = a.get? i := rfl
@[simp] theorem get?_eq_getElem? (a : Array α) (i : Nat) : a.get? i = a[i]? := rfl
theorem getElem_fin_eq_data_get (a : Array α) (i : Fin _) : a[i] = a.data.get i := rfl

theorem getElem?_eq_getElem (a : Array α) (i : Nat) (h : i < a.size) : a[i]? = a[i] :=
  getElem?_pos ..

theorem get?_len_le (a : Array α) (i : Nat) (h : a.size ≤ i) : a[i]? = none := by
  simp [getElem?_neg, h]

theorem getElem_eq_data_get (a : Array α) (h : i < a.size) : a[i] = a.data.get ⟨i, h⟩ := by
  by_cases i < a.size <;> simp [*] <;> rfl

theorem getElem?_eq_data_get? (a : Array α) (i : Nat) : a[i]? = a.data.get? i := by
  by_cases i < a.size <;> simp_all [getElem?_pos, getElem?_neg, List.get?_eq_get, eq_comm] <;> rfl

theorem get?_eq_data_get? (a : Array α) (i : Nat) : a.get? i = a.data.get? i :=
  getElem?_eq_data_get? ..

theorem get_push_lt (a : Array α) (x : α) (i : Nat) (h : i < a.size) :
    haveI : i < (a.push x).size := by simp [*, Nat.lt_succ, Nat.le_of_lt]
    (a.push x)[i] = a[i] := by
  simp only [push, getElem_eq_data_get, List.concat_eq_append, List.get_append, h]

@[simp] theorem get_push_eq (a : Array α) (x : α) : (a.push x)[a.size] = x := by
  simp only [push, getElem_eq_data_get, List.concat_eq_append]
  rw [List.get_append_right] <;> simp [getElem_eq_data_get]

theorem get?_push_lt (a : Array α) (x : α) (i : Nat) (h : i < a.size) :
    (a.push x)[i]? = some a[i] := by
  rw [getElem?_pos, get_push_lt]

theorem get?_push_eq (a : Array α) (x : α) : (a.push x)[a.size]? = some x := by
  rw [getElem?_pos, get_push_eq]

theorem get_push (a : Array α) (x : α) (i : Nat) (h : i < (a.push x).size) :
    (a.push x)[i] = if h : i < a.size then a[i] else x := by
  if h : i < a.size then
    simp [get_push_lt, h]
  else
    have : i = a.size := by apply Nat.le_antisymm <;> simp_all [Nat.lt_succ]
    simp [get_push_lt, this]

@[simp] theorem get_set_eq (a : Array α) (i : Nat) (h : i < a.size) (v : α) :
    (a.set ⟨i, h⟩ v)[i]'(by simp [*]) = v := by
  simp only [set, getElem_eq_data_get, List.get_set_eq]

@[simp] theorem get_set_ne (a : Array α) {i j : Nat} (v : α) (hi : i < a.size) (hj : j < a.size)
    (h : i ≠ j) : (a.set ⟨i, hi⟩ v)[j]'(by simp [*]) = a[j] := by
  simp only [set, getElem_eq_data_get, List.get_set_ne h]

@[simp] theorem get?_set_eq (a : Array α) (i : Nat) (h : i < a.size) (v : α) :
    (a.set ⟨i, h⟩ v)[i]? = v := by
  simp [getElem?_pos, *]

@[simp] theorem get?_set_ne (a : Array α) {i j : Nat} (v : α) (hi : i < a.size)
    (h : i ≠ j) : (a.set ⟨i, hi⟩ v)[j]? = a[j]? := by
  by_cases j < a.size <;> simp [getElem?_pos, getElem?_neg, *]

theorem get?_set (a : Array α) (i j : Nat) (hi : i < a.size) (v : α) :
    (a.set ⟨i, hi⟩ v)[j]? = if i = j then some v else a[j]? := by
  by_cases i = j <;> simp [*]

theorem get_set (a : Array α) (i j : Nat) (hi : i < a.size) (hj : j < a.size) (v : α) :
    (a.set ⟨i, hi⟩ v)[j]'(by simp [*]) = if i = j then v else a[j] := by
  by_cases i = j <;> simp [*]

theorem SatisfiesM_mapIdxM [Monad m] [LawfulMonad m] (as : Array α) (f : Fin as.size → α → m β)
    (p : Fin as.size → α → β → Prop) (hp : ∀ i a, SatisfiesM (p i a) (f i a)) :
    SatisfiesM (fun arr => ∃ eq : arr.size = as.size, ∀ i h, p ⟨i, h⟩ (as[i]'h) (arr[i]'(eq ▸ h)))
      (Array.mapIdxM as f) := by
  let rec go {bs i j h} (h₁ : j = bs.size) (h₂ : ∀ i h h', p ⟨i, h⟩ (as[i]'h) bs[i]) :
    SatisfiesM (fun arr => ∃ eq : arr.size = as.size, ∀ i h, p ⟨i, h⟩ (as[i]'h) (arr[i]'(eq ▸ h)))
      (Array.mapIdxM.map as f i j h bs) := by
    induction i generalizing j bs with simp [mapIdxM.map]
    | zero => exact .pure ⟨h₁ ▸ (Nat.zero_add _).symm.trans h, fun _ _ => h₂ ..⟩
    | succ i ih =>
      refine (hp _ _).bind fun b hb => ih (by simp [h₁]) fun i hi hi' => ?_
      simp at hi'; simp [get_push]; split
      case _ h => exact h₂ _ _ h
      case _ h => cases h₁.symm ▸ (Nat.le_or_eq_or_le_succ hi').resolve_left h; exact hb
  simp [mapIdxM]; exact go rfl fun.

@[simp] theorem size_mapIdx (a : Array α) (f : Fin a.size → α → β) : (a.mapIdx f).size = a.size :=
  (SatisfiesM_Id_eq.1 (SatisfiesM_mapIdxM _ _ _ fun _ _ => .trivial)).1

@[simp] theorem getElem_mapIdx (a : Array α) (f : Fin a.size → α → β) (i : Nat) (h) :
    haveI : i < a.size := by simp_all
    (a.mapIdx f)[i]'h = f ⟨i, this⟩ a[i] := by
  have := SatisfiesM_mapIdxM a f (fun i a b => b = f i a) fun _ _ => SatisfiesM_Id_eq.2 rfl
  exact (SatisfiesM_Id_eq.1 this).2 i _

@[simp] theorem size_swap! (a : Array α) (i j) (hi : i < a.size) (hj : j < a.size) :
    (a.swap! i j).size = a.size := by simp [swap!, hi, hj]

theorem size_reverse_rev (mid i) (a : Array α) (h : mid ≤ a.size) :
    (Array.reverse.rev a.size mid a i).size = a.size :=
  if hi : i < mid then by
    unfold Array.reverse.rev
    have : i < a.size := Nat.lt_of_lt_of_le hi h
    have : a.size - i - 1 < a.size := Nat.sub_lt_self i.zero_lt_succ this
    have := Array.size_reverse_rev mid (i+1) (a.swap! i (a.size - i - 1))
    simp_all
  else by
    unfold Array.reverse.rev
    simp [dif_neg hi]
termination_by _ => mid - i

@[simp] theorem size_reverse (a : Array α) : a.reverse.size = a.size := by
  have := size_reverse_rev (a.size / 2) 0 a (Nat.div_le_self ..)
  simp only [reverse, this]

theorem reverse'.termination {i j : Nat} (h : i < j) : j - 1 - (i + 1) < j - i := by
  rw [Nat.sub_sub, Nat.add_comm]
  exact Nat.lt_of_le_of_lt (Nat.pred_le _) (Nat.sub_succ_lt_self _ _ h)

/-- Reverse of an array. TODO: remove when this lands in core -/
def reverse' (as : Array α) : Array α :=
  if h : as.size ≤ 1 then
    as
  else
    loop as 0 ⟨as.size - 1, Nat.pred_lt (mt (fun h : as.size = 0 => h ▸ by decide) h)⟩
where
  /-- Reverses the subsegment `as[i:j+1]` (that is, indices `i` to `j` inclusive) of `as`. -/
  loop (as : Array α) (i : Nat) (j : Fin as.size) :=
    if h : i < j then
      have := reverse'.termination h
      let as := as.swap ⟨i, Nat.lt_trans h j.2⟩ j
      have : j-1 < as.size := by rw [size_swap]; exact Nat.lt_of_le_of_lt (Nat.pred_le _) j.2
      loop as (i+1) ⟨j-1, this⟩
    else
      as
termination_by _ => j - i

private theorem fin_cast_val (e : n = n') (i : Fin n) : (e ▸ i).1 = i.1 := by cases e; rfl

@[simp] theorem size_reverse' (a : Array α) : a.reverse'.size = a.size := by
  let rec go (as : Array α) (i j) : (reverse'.loop as i j).size = as.size := by
    rw [reverse'.loop]
    if h : i < j then
      have := reverse'.termination h
      simp [(go · (i+1) ⟨j-1, ·⟩), h]
    else simp [h]
  simp only [reverse']; split <;> simp [go]
termination_by _ => j - i

@[simp] theorem reverse'_data (a : Array α) : a.reverse'.data = a.data.reverse := by
  let rec go (as : Array α) (i j hj)
      (h : i + j + 1 = a.size) (h₂ : as.size = a.size)
      (H : ∀ k, as.data.get? k = if i ≤ k ∧ k ≤ j then a.data.get? k else a.data.reverse.get? k)
      (k) : (reverse'.loop as i ⟨j, hj⟩).data.get? k = a.data.reverse.get? k := by
    rw [reverse'.loop]; dsimp; split <;> rename_i h₁
    · have := reverse'.termination h₁
      match j with | j+1 => ?_
      simp [Nat.add_sub_cancel] at *
      simp; rw [(go · (i+1) j)]
      · rwa [Nat.add_right_comm i]
      · simp [size_swap, h₂]
      · intro k
        rw [swap, ← getElem?_eq_data_get?, get?_set, get?_set]
        simp [getElem?_eq_data_get?, getElem_eq_data_get, ← List.get?_eq_get, fin_cast_val, H,
          Nat.le_of_lt h₁]
        split <;> rename_i h₂
        · simp [← h₂, Nat.not_le.2 (Nat.lt_succ_self _)]
          exact (List.get?_reverse' _ _ (Eq.trans (by simp_arith) h)).symm
        split <;> rename_i h₃
        · simp [← h₃, Nat.not_le.2 (Nat.lt_succ_self _)]
          exact (List.get?_reverse' _ _ (Eq.trans (by simp_arith) h)).symm
        simp only [Nat.succ_le, Nat.lt_iff_le_and_ne.trans (and_iff_left h₃),
          Nat.lt_succ.symm.trans (Nat.lt_iff_le_and_ne.trans (and_iff_left (Ne.symm h₂)))]
    · rw [H]; split <;> rename_i h₂
      · cases Nat.le_antisymm (Nat.not_lt.1 h₁) (Nat.le_trans h₂.1 h₂.2)
        cases Nat.le_antisymm h₂.1 h₂.2
        exact (List.get?_reverse' _ _ h).symm
      · rfl
  simp only [reverse']; split
  case _ h => match a, h with | ⟨[]⟩, _ | ⟨[_]⟩, _ => rfl
  case _ =>
    have := Nat.sub_add_cancel (Nat.le_of_not_le ‹_›)
    refine List.ext <| go _ _ _ _ (by simp [this]) rfl fun k => ?_
    split; {rfl}; rename_i h
    simp [← show k < _ + 1 ↔ _ from Nat.lt_succ (n := a.size - 1), this] at h
    rw [List.get?_eq_none.2 ‹_›, List.get?_eq_none.2 (a.data.length_reverse ▸ ‹_›)]
termination_by _ => j - i

@[simp] theorem size_ofFn_go {n} (f : Fin n → α) (i acc) :
    (ofFn.go f i acc).size = acc.size + (n - i) := by
  if hin : i < n then
    unfold ofFn.go
    have : 1 + (n - (i + 1)) = n - i :=
      Nat.sub_sub .. ▸ Nat.add_sub_cancel' (Nat.le_sub_of_add_le (Nat.add_comm .. ▸ hin))
    rw [dif_pos hin, size_ofFn_go f (i+1), size_push, Nat.add_assoc, this]
  else
    have : n - i = 0 := Nat.sub_eq_zero_of_le (Nat.le_of_not_lt hin)
    unfold ofFn.go
    simp [hin, this]
termination_by size_ofFn_go n f i acc => n - i

@[simp] theorem size_ofFn (f : Fin n → α) : (ofFn f).size = n := by simp [ofFn]

theorem getElem_ofFn_go (f : Fin n → α) (i) {acc k}
    (hki : k < n) (hin : i ≤ n) (hi : i = acc.size)
    (hacc : ∀ j, ∀ hj : j < acc.size, acc[j] = f ⟨j, Nat.lt_of_lt_of_le hj (hi ▸ hin)⟩) :
    haveI : acc.size + (n - acc.size) = n := Nat.add_sub_cancel' (hi ▸ hin)
    (ofFn.go f i acc)[k]'(by simp [*]) = f ⟨k, hki⟩ := by
  unfold ofFn.go
  if hin : i < n then
    have : 1 + (n - (i + 1)) = n - i :=
      Nat.sub_sub .. ▸ Nat.add_sub_cancel' (Nat.le_sub_of_add_le (Nat.add_comm .. ▸ hin))
    simp only [dif_pos hin]
    rw [getElem_ofFn_go f (i+1) _ hin (by simp [*]) (fun j hj => ?hacc)]
    cases (Nat.lt_or_eq_of_le <| Nat.le_of_lt_succ (by simpa using hj)) with
    | inl hj => simp [get_push, hj, hacc j hj]
    | inr hj => simp [get_push, *]
  else
    simp [hin, hacc k (Nat.lt_of_lt_of_le hki (Nat.le_of_not_lt (hi ▸ hin)))]
termination_by _ _ i _ _ _ _ _ _ => n - i

@[simp] theorem getElem_ofFn (f : Fin n → α) (i : Nat) (h) :
    (ofFn f)[i] = f ⟨i, size_ofFn f ▸ h⟩ :=
  getElem_ofFn_go _ _ _ (by simp) (by simp) fun.

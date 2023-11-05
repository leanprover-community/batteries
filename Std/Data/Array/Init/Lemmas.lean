/-
Copyright (c) 2022 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Std.Tactic.NoMatch
import Std.Tactic.HaveI
import Std.Classes.LawfulMonad
import Std.Data.Nat.Init.Lemmas
import Std.Data.List.Init.Lemmas
import Std.Data.Array.Init.Basic

/-!
## Bootstrapping theorems about arrays

This file contains some theorems about `Array` and `List` needed for `Std.List.Basic`.
-/

namespace Array

attribute [simp] data_toArray uset

@[simp] theorem mkEmpty_eq (α n) : @mkEmpty α n = #[] := rfl

@[simp] theorem size_toArray (as : List α) : as.toArray.size = as.length := by simp [size]

@[simp] theorem size_mk (as : List α) : (Array.mk as).size = as.length := by simp [size]

theorem getElem_eq_data_get (a : Array α) (h : i < a.size) : a[i] = a.data.get ⟨i, h⟩ := by
  by_cases i < a.size <;> (try simp [*]) <;> rfl

theorem foldlM_eq_foldlM_data.aux [Monad m]
    (f : β → α → m β) (arr : Array α) (i j) (H : arr.size ≤ i + j) (b) :
    foldlM.loop f arr arr.size (Nat.le_refl _) i j b = (arr.data.drop j).foldlM f b := by
  unfold foldlM.loop
  split; split
  · cases Nat.not_le_of_gt ‹_› (Nat.zero_add _ ▸ H)
  · rename_i i; rw [Nat.succ_add] at H
    simp [foldlM_eq_foldlM_data.aux f arr i (j+1) H]
    conv => rhs; rw [← List.get_drop_eq_drop _ _ ‹_›]
  · rw [List.drop_length_le (Nat.ge_of_not_lt ‹_›)]; rfl

theorem foldlM_eq_foldlM_data [Monad m]
    (f : β → α → m β) (init : β) (arr : Array α) :
    arr.foldlM f init = arr.data.foldlM f init := by
  simp [foldlM, foldlM_eq_foldlM_data.aux]

theorem foldl_eq_foldl_data (f : β → α → β) (init : β) (arr : Array α) :
    arr.foldl f init = arr.data.foldl f init :=
  List.foldl_eq_foldlM .. ▸ foldlM_eq_foldlM_data ..

theorem foldrM_eq_reverse_foldlM_data.aux [Monad m]
    (f : α → β → m β) (arr : Array α) (init : β) (i h) :
    (arr.data.take i).reverse.foldlM (fun x y => f y x) init = foldrM.fold f arr 0 i h init := by
  unfold foldrM.fold
  match i with
  | 0 => simp [List.foldlM, List.take]
  | i+1 => rw [← List.take_concat_get _ _ h]; simp [← (aux f arr · i)]; rfl

theorem foldrM_eq_reverse_foldlM_data [Monad m] (f : α → β → m β) (init : β) (arr : Array α) :
    arr.foldrM f init = arr.data.reverse.foldlM (fun x y => f y x) init := by
  have : arr = #[] ∨ 0 < arr.size :=
    match arr with | ⟨[]⟩ => .inl rfl | ⟨a::l⟩ => .inr (Nat.zero_lt_succ _)
  match arr, this with | _, .inl rfl => rfl | arr, .inr h => ?_
  simp [foldrM, h, ← foldrM_eq_reverse_foldlM_data.aux, List.take_length]

theorem foldrM_eq_foldrM_data [Monad m]
    (f : α → β → m β) (init : β) (arr : Array α) :
    arr.foldrM f init = arr.data.foldrM f init := by
  rw [foldrM_eq_reverse_foldlM_data, List.foldlM_reverse]

theorem foldr_eq_foldr_data (f : α → β → β) (init : β) (arr : Array α) :
    arr.foldr f init = arr.data.foldr f init :=
  List.foldr_eq_foldrM .. ▸ foldrM_eq_foldrM_data ..

@[simp] theorem push_data (arr : Array α) (a : α) : (arr.push a).data = arr.data ++ [a] := by
  simp [push, List.concat_eq_append]

theorem foldrM_push [Monad m] (f : α → β → m β) (init : β) (arr : Array α) (a : α) :
    (arr.push a).foldrM f init = f a init >>= arr.foldrM f := by
  simp [foldrM_eq_reverse_foldlM_data, -size_push]

@[simp] theorem foldrM_push' [Monad m] (f : α → β → m β) (init : β) (arr : Array α) (a : α) :
    (arr.push a).foldrM f init (start := arr.size + 1) = f a init >>= arr.foldrM f := by
  simp [← foldrM_push]

theorem foldr_push (f : α → β → β) (init : β) (arr : Array α) (a : α) :
    (arr.push a).foldr f init = arr.foldr f (f a init) := foldrM_push ..

@[simp] theorem foldr_push' (f : α → β → β) (init : β) (arr : Array α) (a : α) :
    (arr.push a).foldr f init (start := arr.size + 1) = arr.foldr f (f a init) := foldrM_push' ..

@[simp] theorem toListAppend_eq (arr : Array α) (l) : arr.toListAppend l = arr.data ++ l := by
  simp [toListAppend, foldr_eq_foldr_data]

@[simp] theorem toList_eq (arr : Array α) : arr.toList = arr.data := by
  simp [toList, foldr_eq_foldr_data]

/-- A more efficient version of `arr.toList.reverse`. -/
@[inline] def toListRev (arr : Array α) : List α := arr.foldl (fun l t => t :: l) []

@[simp] theorem toListRev_eq (arr : Array α) : arr.toListRev = arr.data.reverse := by
  rw [toListRev, foldl_eq_foldl_data, ← List.foldr_reverse, List.foldr_self]

theorem SatisfiesM_foldlM [Monad m] [LawfulMonad m]
    {as : Array α} (motive : Nat → β → Prop) {init : β} (h0 : motive 0 init) {f : β → α → m β}
    (hf : ∀ i : Fin as.size, ∀ b, motive i.1 b → SatisfiesM (motive (i.1 + 1)) (f b as[i])) :
    SatisfiesM (motive as.size) (as.foldlM f init) := by
  let rec go {i j b} (h₁ : j ≤ as.size) (h₂ : as.size ≤ i + j) (H : motive j b) :
    SatisfiesM (motive as.size) (foldlM.loop f as as.size (Nat.le_refl _) i j b) := by
    unfold foldlM.loop; split
    · next hj =>
      split
      · cases Nat.not_le_of_gt (by simp [hj]) h₂
      · exact (hf ⟨j, hj⟩ b H).bind fun _ => go hj (by rwa [Nat.succ_add] at h₂)
    · next hj => exact Nat.le_antisymm h₁ (Nat.ge_of_not_lt hj) ▸ .pure H
  simp [foldlM]; exact go (Nat.zero_le _) (Nat.le_refl _) h0

theorem foldl_induction
    {as : Array α} (motive : Nat → β → Prop) {init : β} (h0 : motive 0 init) {f : β → α → β}
    (hf : ∀ i : Fin as.size, ∀ b, motive i.1 b → motive (i.1 + 1) (f b as[i])) :
    motive as.size (as.foldl f init) := by
  have := SatisfiesM_foldlM (m := Id) (as := as) (f := f) motive h0
  simp [SatisfiesM_Id_eq] at this
  exact this hf

theorem get_push_lt (a : Array α) (x : α) (i : Nat) (h : i < a.size) :
    haveI : i < (a.push x).size := by simp [*, Nat.lt_succ_of_le, Nat.le_of_lt]
    (a.push x)[i] = a[i] := by
  simp only [push, getElem_eq_data_get, List.concat_eq_append, List.get_append_left, h]

@[simp] theorem get_push_eq (a : Array α) (x : α) : (a.push x)[a.size] = x := by
  simp only [push, getElem_eq_data_get, List.concat_eq_append]
  rw [List.get_append_right] <;> simp [getElem_eq_data_get]

theorem get_push (a : Array α) (x : α) (i : Nat) (h : i < (a.push x).size) :
    (a.push x)[i] = if h : i < a.size then a[i] else x := by
  if h' : i < a.size then
    simp [get_push_lt, h']
  else
    simp at h
    simp [get_push_lt, Nat.le_antisymm (Nat.le_of_lt_succ h) (Nat.ge_of_not_lt h')]

theorem mapM_eq_foldlM [Monad m] [LawfulMonad m] (f : α → m β) (arr : Array α) :
    arr.mapM f = arr.foldlM (fun bs a => bs.push <$> f a) #[] := by
  rw [mapM, aux, foldlM_eq_foldlM_data]; rfl
where
  aux (i r) :
      mapM.map f arr i r = (arr.data.drop i).foldlM (fun bs a => bs.push <$> f a) r := by
    unfold mapM.map; split
    · rw [← List.get_drop_eq_drop _ i ‹_›]
      simp [aux (i+1), map_eq_pure_bind]; rfl
    · rw [List.drop_length_le (Nat.ge_of_not_lt ‹_›)]; rfl
termination_by aux => arr.size - i

theorem SatisfiesM_mapM [Monad m] [LawfulMonad m] (as : Array α) (f : α → m β)
    (motive : Nat → Prop) (h0 : motive 0)
    (p : Fin as.size → β → Prop)
    (hs : ∀ i, motive i.1 → SatisfiesM (p i · ∧ motive (i + 1)) (f as[i])) :
    SatisfiesM
      (fun arr => motive as.size ∧ ∃ eq : arr.size = as.size, ∀ i h, p ⟨i, h⟩ (arr[i]'(eq ▸ h)))
      (Array.mapM f as) := by
  rw [mapM_eq_foldlM]
  refine SatisfiesM_foldlM (m := m) (β := Array β)
    (motive := fun i arr => motive i ∧ arr.size = i ∧ ∀ i h2, p i (arr[i.1]'h2)) ?z ?s
    |>.imp fun ⟨h₁, eq, h₂⟩ => ⟨h₁, eq, fun _ _ => h₂ ..⟩
  · case z => exact ⟨h0, rfl, fun.⟩
  · case s =>
    intro ⟨i, hi⟩ arr ⟨ih₁, eq, ih₂⟩
    refine (hs _ ih₁).map fun ⟨h₁, h₂⟩ => ⟨h₂, by simp [eq], fun j hj => ?_⟩
    simp [get_push] at hj ⊢; split; {apply ih₂}
    cases j; cases (Nat.le_or_eq_of_le_succ hj).resolve_left ‹_›; cases eq; exact h₁

theorem SatisfiesM_mapM' [Monad m] [LawfulMonad m] (as : Array α) (f : α → m β)
    (p : Fin as.size → β → Prop)
    (hs : ∀ i, SatisfiesM (p i) (f as[i])) :
    SatisfiesM
      (fun arr => ∃ eq : arr.size = as.size, ∀ i h, p ⟨i, h⟩ (arr[i]'(eq ▸ h)))
      (Array.mapM f as) :=
  (SatisfiesM_mapM _ _ (fun _ => True) trivial _ (fun _ h => (hs _).imp (⟨·, h⟩))).imp (·.2)

theorem size_mapM [Monad m] [LawfulMonad m] (f : α → m β) (as : Array α) :
    SatisfiesM (fun arr => arr.size = as.size) (Array.mapM f as) :=
  (SatisfiesM_mapM' _ _ (fun _ _ => True) (fun _ => .trivial)).imp (·.1)

@[simp] theorem map_data (f : α → β) (arr : Array α) : (arr.map f).data = arr.data.map f := by
  rw [map, mapM_eq_foldlM]
  apply congrArg data (foldl_eq_foldl_data (fun bs a => push bs (f a)) #[] arr) |>.trans
  have H (l arr) : List.foldl (fun bs a => push bs (f a)) arr l = ⟨arr.data ++ l.map f⟩ := by
    induction l generalizing arr <;> simp [*]
  simp [H]

@[simp] theorem size_map (f : α → β) (arr : Array α) : (arr.map f).size = arr.size := by
  simp [size]

@[simp] theorem getElem_map (f : α → β) (arr : Array α) (i : Nat) (h) :
    ((arr.map f)[i]'h) = f (arr[i]'(size_map .. ▸ h)) := by
  have := SatisfiesM_mapM' (m := Id) arr f (fun i b => b = f (arr[i]))
  simp [SatisfiesM_Id_eq] at this
  exact this.2 i (size_map .. ▸ h)

@[simp] theorem pop_data (arr : Array α) : arr.pop.data = arr.data.dropLast := rfl

@[simp] theorem append_eq_append (arr arr' : Array α) : arr.append arr' = arr ++ arr' := rfl

@[simp] theorem append_data (arr arr' : Array α) :
    (arr ++ arr').data = arr.data ++ arr'.data := by
  rw [← append_eq_append]; unfold Array.append
  rw [foldl_eq_foldl_data]
  induction arr'.data generalizing arr <;> simp [*]

@[simp] theorem appendList_eq_append
    (arr : Array α) (l : List α) : arr.appendList l = arr ++ l := rfl

@[simp] theorem appendList_data (arr : Array α) (l : List α) :
    (arr ++ l).data = arr.data ++ l := by
  rw [← appendList_eq_append]; unfold Array.appendList
  induction l generalizing arr <;> simp [*]

theorem foldl_data_eq_bind (l : List α) (acc : Array β)
    (F : Array β → α → Array β) (G : α → List β)
    (H : ∀ acc a, (F acc a).data = acc.data ++ G a) :
    (l.foldl F acc).data = acc.data ++ l.bind G := by
  induction l generalizing acc <;> simp [*, List.bind]

theorem foldl_data_eq_map (l : List α) (acc : Array β) (G : α → β) :
    (l.foldl (fun acc a => acc.push (G a)) acc).data = acc.data ++ l.map G := by
  induction l generalizing acc <;> simp [*]

theorem size_uset (a : Array α) (v i h) : (uset a i v h).size = a.size := by simp

theorem anyM_eq_anyM_loop [Monad m] (p : α → m Bool) (as : Array α) (start stop) :
    anyM p as start stop = anyM.loop p as (min stop as.size) (Nat.min_le_right ..) start := by
  simp only [anyM, Nat.min_def]; split <;> rfl

theorem anyM_stop_le_start [Monad m] (p : α → m Bool) (as : Array α) (start stop)
    (h : min stop as.size ≤ start) : anyM p as start stop = pure false := by
  rw [anyM_eq_anyM_loop, anyM.loop, dif_neg (Nat.not_lt.2 h)]

theorem SatisfiesM_anyM [Monad m] [LawfulMonad m] (p : α → m Bool) (as : Array α) (start stop)
    (hstart : start ≤ min stop as.size) (tru : Prop) (fal : Nat → Prop) (h0 : fal start)
    (hp : ∀ i : Fin as.size, i.1 < stop → fal i.1 →
      SatisfiesM (bif · then tru else fal (i + 1)) (p as[i])) :
    SatisfiesM
      (fun res => bif res then tru else fal (min stop as.size))
      (anyM p as start stop) := by
  let rec go {stop j} (hj' : j ≤ stop) (hstop : stop ≤ as.size) (h0 : fal j)
    (hp : ∀ i : Fin as.size, i.1 < stop → fal i.1 →
      SatisfiesM (bif · then tru else fal (i + 1)) (p as[i])) :
    SatisfiesM
      (fun res => bif res then tru else fal stop)
      (anyM.loop p as stop hstop j) := by
    unfold anyM.loop; split
    · next hj =>
      exact (hp ⟨j, Nat.lt_of_lt_of_le hj hstop⟩ hj h0).bind fun
        | true, h => .pure h
        | false, h => go hj hstop h hp
    · next hj => exact .pure <| Nat.le_antisymm hj' (Nat.ge_of_not_lt hj) ▸ h0
  simp only [Array.anyM_eq_anyM_loop]
  exact go hstart _ h0 fun i hi => hp i <| Nat.lt_of_lt_of_le hi <| Nat.min_le_left ..
termination_by go => stop - j

theorem SatisfiesM_anyM_iff_exists [Monad m] [LawfulMonad m]
    (p : α → m Bool) (as : Array α) (start stop) (q : Fin as.size → Prop)
    (hp : ∀ i : Fin as.size, start ≤ i.1 → i.1 < stop → SatisfiesM (· = true ↔ q i) (p as[i])) :
    SatisfiesM
      (fun res => res = true ↔ ∃ i : Fin as.size, start ≤ i.1 ∧ i.1 < stop ∧ q i)
      (anyM p as start stop) := by
  cases Nat.le_total start (min stop as.size) with
  | inl hstart =>
    refine (SatisfiesM_anyM _ _ _ _ hstart
      (fal := fun j => start ≤ j ∧ ¬ ∃ i : Fin as.size, start ≤ i.1 ∧ i.1 < j ∧ q i)
      (tru := ∃ i : Fin as.size, start ≤ i.1 ∧ i.1 < stop ∧ q i) ?_ ?_).imp ?_
    · exact ⟨Nat.le_refl _, fun ⟨i, h₁, h₂, _⟩ => (Nat.not_le_of_gt h₂ h₁).elim⟩
    · refine fun i h₂ ⟨h₁, h₃⟩ => (hp _ h₁ h₂).imp fun hq => ?_
      unfold cond; split <;> simp at hq
      · exact ⟨_, h₁, h₂, hq⟩
      · refine ⟨Nat.le_succ_of_le h₁, h₃.imp fun ⟨j, h₃, h₄, h₅⟩ => ⟨j, h₃, ?_, h₅⟩⟩
        refine Nat.lt_of_le_of_ne (Nat.le_of_lt_succ h₄) fun e => hq (Fin.eq_of_val_eq e ▸ h₅)
    · intro
      | true, h => simp only [true_iff]; exact h
      | false, h =>
        simp only [false_iff]
        exact h.2.imp fun ⟨j, h₁, h₂, hq⟩ => ⟨j, h₁, Nat.lt_min.2 ⟨h₂, j.2⟩, hq⟩
  | inr hstart =>
    rw [anyM_stop_le_start (h := hstart)]
    refine .pure ?_; simp; intro j h₁ h₂
    cases Nat.not_lt.2 (Nat.le_trans hstart h₁) (Nat.lt_min.2 ⟨h₂, j.2⟩)

theorem any_iff_exists (p : α → Bool) (as : Array α) (start stop) :
    any as p start stop ↔ ∃ i : Fin as.size, start ≤ i.1 ∧ i.1 < stop ∧ p as[i] := by
  have := SatisfiesM_anyM_iff_exists (m := Id) p as start stop (p as[·]) (by simp)
  rwa [SatisfiesM_Id_eq] at this

theorem any_eq_true (p : α → Bool) (as : Array α) :
    any as p ↔ ∃ i : Fin as.size, p as[i] := by simp [any_iff_exists, Fin.isLt]

theorem mem_def (a : α) (as : Array α) : a ∈ as ↔ a ∈ as.data :=
  ⟨fun | .mk h => h, Array.Mem.mk⟩

theorem any_def {p : α → Bool} (as : Array α) : as.any p = as.data.any p := by
  rw [Bool.eq_iff_iff, any_eq_true, List.any_eq_true]; simp only [List.mem_iff_get]
  exact ⟨fun ⟨i, h⟩ => ⟨_, ⟨i, rfl⟩, h⟩, fun ⟨_, ⟨i, rfl⟩, h⟩ => ⟨i, h⟩⟩

theorem contains_def [DecidableEq α] {a : α} {as : Array α} : as.contains a ↔ a ∈ as := by
  rw [mem_def, contains, any_def, List.any_eq_true]; simp [and_comm]

instance [DecidableEq α] (a : α) (as : Array α) : Decidable (a ∈ as) :=
  decidable_of_iff _ contains_def

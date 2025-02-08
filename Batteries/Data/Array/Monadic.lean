/-
Copyright (c) 2021 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Mario Carneiro, Gabriel Ebner
-/
import Batteries.Classes.SatisfiesM
import Batteries.Util.ProofWanted

/-!
# Results about monadic operations on `Array`, in terms of `SatisfiesM`.

The pure versions of these theorems are proved in `Batteries.Data.Array.Lemmas` directly,
in order to minimize dependence on `SatisfiesM`.
-/

namespace Array

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

theorem SatisfiesM_mapM [Monad m] [LawfulMonad m] (as : Array α) (f : α → m β)
    (motive : Nat → Prop) (h0 : motive 0)
    (p : Fin as.size → β → Prop)
    (hs : ∀ i, motive i.1 → SatisfiesM (p i · ∧ motive (i + 1)) (f as[i])) :
    SatisfiesM
      (fun arr => motive as.size ∧ ∃ eq : arr.size = as.size, ∀ i h, p ⟨i, h⟩ arr[i])
      (Array.mapM f as) := by
  rw [mapM_eq_foldlM]
  refine SatisfiesM_foldlM (m := m) (β := Array β)
    (motive := fun i arr => motive i ∧ arr.size = i ∧ ∀ i h2, p i (arr[i.1]'h2)) ?z ?s
    |>.imp fun ⟨h₁, eq, h₂⟩ => ⟨h₁, eq, fun _ _ => h₂ ..⟩
  · case z => exact ⟨h0, rfl, nofun⟩
  · case s =>
    intro ⟨i, hi⟩ arr ⟨ih₁, eq, ih₂⟩
    refine (hs _ ih₁).map fun ⟨h₁, h₂⟩ => ⟨h₂, by simp [eq], fun j hj => ?_⟩
    simp [getElem_push] at hj ⊢; split; {apply ih₂}
    cases j; cases (Nat.le_or_eq_of_le_succ hj).resolve_left ‹_›; cases eq; exact h₁

theorem SatisfiesM_mapM' [Monad m] [LawfulMonad m] (as : Array α) (f : α → m β)
    (p : Fin as.size → β → Prop)
    (hs : ∀ i, SatisfiesM (p i) (f as[i])) :
    SatisfiesM
      (fun arr => ∃ eq : arr.size = as.size, ∀ i h, p ⟨i, h⟩ arr[i])
      (Array.mapM f as) :=
  (SatisfiesM_mapM _ _ (fun _ => True) trivial _ (fun _ h => (hs _).imp (⟨·, h⟩))).imp (·.2)

theorem size_mapM [Monad m] [LawfulMonad m] (f : α → m β) (as : Array α) :
    SatisfiesM (fun arr => arr.size = as.size) (Array.mapM f as) :=
  (SatisfiesM_mapM' _ _ (fun _ _ => True) (fun _ => .trivial)).imp (·.1)

proof_wanted size_mapIdxM [Monad m] [LawfulMonad m] (as : Array α) (f : Nat → α → m β) :
    SatisfiesM (fun arr => arr.size = as.size) (Array.mapIdxM f as)

proof_wanted size_mapFinIdxM [Monad m] [LawfulMonad m]
    (as : Array α) (f : (i : Nat) → α → (h : i < as.size) → m β) :
    SatisfiesM (fun arr => arr.size = as.size) (Array.mapFinIdxM as f)

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
    termination_by stop - j
  simp only [Array.anyM_eq_anyM_loop]
  exact go hstart _ h0 fun i hi => hp i <| Nat.lt_of_lt_of_le hi <| Nat.min_le_left ..

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
        simp only [false_iff, reduceCtorEq]
        exact h.2.imp fun ⟨j, h₁, h₂, hq⟩ => ⟨j, h₁, Nat.lt_min.2 ⟨h₂, j.2⟩, hq⟩
  | inr hstart =>
    rw [anyM_stop_le_start (h := hstart)]
    refine .pure ?_; simp; intro j h₁ h₂
    cases Nat.not_lt.2 (Nat.le_trans hstart h₁) (Nat.lt_min.2 ⟨h₂, j.2⟩)

theorem SatisfiesM_foldrM [Monad m] [LawfulMonad m]
    {as : Array α} (motive : Nat → β → Prop)
    {init : β} (h0 : motive as.size init) {f : α → β → m β}
    (hf : ∀ i : Fin as.size, ∀ b, motive (i.1 + 1) b → SatisfiesM (motive i.1) (f as[i] b)) :
    SatisfiesM (motive 0) (as.foldrM f init) := by
  let rec go {i b} (hi : i ≤ as.size) (H : motive i b) :
    SatisfiesM (motive 0) (foldrM.fold f as 0 i hi b) := by
    unfold foldrM.fold; simp; split
    · next hi => exact .pure (hi ▸ H)
    · next hi =>
      split; {simp at hi}
      · next i hi' =>
        exact (hf ⟨i, hi'⟩ b H).bind fun _ => go _
  simp [foldrM]; split; {exact go _ h0}
  · next h => exact .pure (Nat.eq_zero_of_not_pos h ▸ h0)

theorem SatisfiesM_mapFinIdxM [Monad m] [LawfulMonad m] (as : Array α)
    (f : (i : Nat) → α → (h : i < as.size) → m β)
    (motive : Nat → Prop) (h0 : motive 0)
    (p : (i : Nat) → β → (h : i < as.size) → Prop)
    (hs : ∀ i h, motive i → SatisfiesM (p i · h ∧ motive (i + 1)) (f i as[i] h)) :
    SatisfiesM
      (fun arr => motive as.size ∧ ∃ eq : arr.size = as.size, ∀ i h, p i arr[i] h)
      (Array.mapFinIdxM as f) := by
  let rec go {bs i j h} (h₁ : j = bs.size) (h₂ : ∀ i h h', p i bs[i] h) (hm : motive j) :
    SatisfiesM
      (fun arr => motive as.size ∧ ∃ eq : arr.size = as.size, ∀ i h, p i arr[i] h)
      (Array.mapFinIdxM.map as f i j h bs) := by
    induction i generalizing j bs with simp [mapFinIdxM.map]
    | zero =>
      have := (Nat.zero_add _).symm.trans h
      exact .pure ⟨this ▸ hm, h₁ ▸ this, fun _ _ => h₂ ..⟩
    | succ i ih =>
      refine (hs _ _ (by exact hm)).bind fun b hb => ih (by simp [h₁]) (fun i hi hi' => ?_) hb.2
      simp at hi'; simp [getElem_push]; split
      · next h => exact h₂ _ _ h
      · next h => cases h₁.symm ▸ (Nat.le_or_eq_of_le_succ hi').resolve_left h; exact hb.1
  simp [mapFinIdxM]; exact go rfl nofun h0

theorem SatisfiesM_mapIdxM [Monad m] [LawfulMonad m] (as : Array α) (f : Nat → α → m β)
    (motive : Nat → Prop) (h0 : motive 0)
    (p : (i : Nat) → β → (h : i < as.size) → Prop)
    (hs : ∀ i h, motive i → SatisfiesM (p i · h ∧ motive (i + 1)) (f i as[i])) :
    SatisfiesM
      (fun arr => motive as.size ∧ ∃ eq : arr.size = as.size, ∀ i h, p i arr[i] h)
      (as.mapIdxM f) :=
  SatisfiesM_mapFinIdxM as (fun i a _ => f i a) motive h0 p hs

theorem size_mapFinIdxM [Monad m] [LawfulMonad m]
    (as : Array α) (f : (i : Nat) → α → (h : i < as.size) → m β) :
    SatisfiesM (fun arr => arr.size = as.size) (Array.mapFinIdxM as f) :=
  (SatisfiesM_mapFinIdxM _ _ (fun _ => True) trivial (fun _ _ _ => True)
    (fun _ _ _ => .of_true fun _ => ⟨trivial, trivial⟩)).imp (·.2.1)

theorem size_mapIdxM [Monad m] [LawfulMonad m] (as : Array α) (f : Nat → α → m β) :
    SatisfiesM (fun arr => arr.size = as.size) (Array.mapIdxM f as) :=
  size_mapFinIdxM _ _

theorem size_modifyM [Monad m] [LawfulMonad m] (a : Array α) (i : Nat) (f : α → m α) :
    SatisfiesM (·.size = a.size) (a.modifyM i f) := by
  unfold modifyM; split
  · exact .bind_pre <| .of_true fun _ => .pure <| by simp only [size_set]
  · exact .pure rfl

end Array

namespace List

theorem filterM_toArray [Monad m] [LawfulMonad m] (l : List α) (p : α → m Bool) :
    l.toArray.filterM p = toArray <$> l.filterM p := by
  simp only [Array.filterM, filterM, foldlM_toArray, bind_pure_comp, Functor.map_map]
  conv => lhs; rw [← reverse_nil]
  generalize [] = acc
  induction l generalizing acc with simp
  | cons x xs ih =>
    congr; funext b
    cases b
    · simp only [Bool.false_eq_true, ↓reduceIte, pure_bind, cond_false]
      exact ih acc
    · simp only [↓reduceIte, ← reverse_cons, pure_bind, cond_true]
      exact ih (x :: acc)

theorem filterRevM_toArray [Monad m] [LawfulMonad m] (l : List α) (p : α → m Bool) :
    l.toArray.filterRevM p = toArray <$> l.filterRevM p := by
  simp [Array.filterRevM, filterRevM]
  rw [← foldlM_reverse, ← foldlM_toArray, ← Array.filterM, filterM_toArray]
  simp only [filterM, bind_pure_comp, Functor.map_map, reverse_toArray, reverse_reverse]

theorem filterMapM_toArray [Monad m] [LawfulMonad m] (l : List α) (f : α → m (Option β)) :
    l.toArray.filterMapM f = toArray <$> l.filterMapM f := by
  simp [Array.filterMapM, filterMapM]
  conv => lhs; rw [← reverse_nil]
  generalize [] = acc
  induction l generalizing acc with simp [filterMapM.loop]
  | cons x xs ih =>
    congr; funext o
    cases o
    · simp only [pure_bind]; exact ih acc
    · simp only [pure_bind]; rw [← List.reverse_cons]; exact ih _

theorem flatMapM_toArray [Monad m] [LawfulMonad m] (l : List α) (f : α → m (Array β)) :
    l.toArray.flatMapM f = toArray <$> l.flatMapM (fun a => Array.toList <$> f a) := by
  simp only [Array.flatMapM, bind_pure_comp, foldlM_toArray, flatMapM]
  conv => lhs; arg 2; change [].reverse.flatten.toArray
  generalize [] = acc
  induction l generalizing acc with
  | nil => simp only [foldlM_nil, flatMapM.loop, map_pure]
  | cons x xs ih =>
    simp only [foldlM_cons, bind_map_left, flatMapM.loop, _root_.map_bind]
    congr; funext a
    conv => lhs; rw [Array.toArray_append, ← flatten_concat, ← reverse_cons]
    exact ih _

theorem mapFinIdxM_toArray [Monad m] [LawfulMonad m] (l : List α)
    (f : (i : Nat) → α → (h : i < l.length) → m β) :
    l.toArray.mapFinIdxM f = toArray <$> l.mapFinIdxM f := by
  let rec go (i : Nat) (acc : Array β) (inv : i + acc.size = l.length) :
      Array.mapFinIdxM.map l.toArray f i acc.size inv acc
      = toArray <$> mapFinIdxM.go l f (l.drop acc.size) acc
        (by simp [Nat.sub_add_cancel (Nat.le.intro (Nat.add_comm _ _ ▸ inv))]) := by
    match i with
    | 0 =>
      rw [Nat.zero_add] at inv
      simp only [Array.mapFinIdxM.map, inv, drop_length, mapFinIdxM.go, map_pure]
    | k + 1 =>
      conv => enter [2, 2, 3]; rw [← getElem_cons_drop l acc.size (by omega)]
      simp only [Array.mapFinIdxM.map, mapFinIdxM.go, _root_.map_bind]
      congr; funext x
      conv => enter [1, 4]; rw [← Array.size_push _ x]
      conv => enter [2, 2, 3]; rw [← Array.size_push _ x]
      refine go k (acc.push x) _
  simp only [Array.mapFinIdxM, mapFinIdxM]
  exact go _ #[] _

theorem mapIdxM_toArray [Monad m] [LawfulMonad m] (l : List α)
    (f : Nat → α → m β) :
    l.toArray.mapIdxM f = toArray <$> l.mapIdxM f := by
  let rec go (bs : List α) (acc : Array β) (inv : bs.length + acc.size = l.length) :
      mapFinIdxM.go l (fun i a h => f i a) bs acc inv = mapIdxM.go f bs acc := by
    match bs with
    | [] => simp only [mapFinIdxM.go, mapIdxM.go]
    | x :: xs => simp only [mapFinIdxM.go, mapIdxM.go, go]
  unfold Array.mapIdxM
  rw [mapFinIdxM_toArray]
  simp only [mapFinIdxM, mapIdxM]
  rw [go]

end List

namespace Array

theorem toList_filterM [Monad m] [LawfulMonad m] (a : Array α) (p : α → m Bool) :
    toList <$> a.filterM p = a.toList.filterM p := by
  rw [List.filterM_toArray]
  simp only [Functor.map_map, id_map']

theorem toList_filterRevM [Monad m] [LawfulMonad m] (a : Array α) (p : α → m Bool) :
    toList <$> a.filterRevM p = a.toList.filterRevM p := by
  rw [List.filterRevM_toArray]
  simp only [Functor.map_map, id_map']

theorem toList_filterMapM [Monad m] [LawfulMonad m] (a : Array α) (f : α → m (Option β)) :
    toList <$> a.filterMapM f = a.toList.filterMapM f := by
  rw [List.filterMapM_toArray]
  simp only [Functor.map_map, id_map']

theorem toList_flatMapM [Monad m] [LawfulMonad m] (a : Array α) (f : α → m (Array β)) :
    toList <$> a.flatMapM f = a.toList.flatMapM (fun a => toList <$> f a) := by
  rw [List.flatMapM_toArray]
  simp only [Functor.map_map, id_map']

theorem toList_mapFinIdxM [Monad m] [LawfulMonad m] (l : Array α)
    (f : (i : Nat) → α → (h : i < l.size) → m β) :
    toList <$> l.mapFinIdxM f = l.toList.mapFinIdxM f := by
  rw [List.mapFinIdxM_toArray]
  simp only [Functor.map_map, id_map']

theorem toList_mapIdxM [Monad m] [LawfulMonad m] (l : Array α)
    (f : Nat → α → m β) :
    toList <$> l.mapIdxM f = l.toList.mapIdxM f := by
  rw [List.mapIdxM_toArray]
  simp only [Functor.map_map, id_map']

end Array

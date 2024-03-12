/-
Copyright (c) 2021 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Mario Carneiro, Gabriel Ebner
-/
import Std.Data.Nat.Lemmas
import Std.Data.List.Lemmas
import Std.Data.Array.Init.Lemmas
import Std.Data.Array.Basic
import Std.Tactic.SeqFocus
import Std.Util.ProofWanted
import Std.Classes.SatisfiesM

/-!
# Results about monadic operations on `Array`.
-/

namespace Array

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

theorem foldr_induction
    {as : Array α} (motive : Nat → β → Prop) {init : β} (h0 : motive as.size init) {f : α → β → β}
    (hf : ∀ i : Fin as.size, ∀ b, motive (i.1 + 1) b → motive i.1 (f as[i] b)) :
    motive 0 (as.foldr f init) := by
  have := SatisfiesM_foldrM (m := Id) (as := as) (f := f) motive h0
  simp [SatisfiesM_Id_eq] at this
  exact this hf


theorem SatisfiesM_mapIdxM [Monad m] [LawfulMonad m] (as : Array α) (f : Fin as.size → α → m β)
    (motive : Nat → Prop) (h0 : motive 0)
    (p : Fin as.size → β → Prop)
    (hs : ∀ i, motive i.1 → SatisfiesM (p i · ∧ motive (i + 1)) (f i as[i])) :
    SatisfiesM
      (fun arr => motive as.size ∧ ∃ eq : arr.size = as.size, ∀ i h, p ⟨i, h⟩ (arr[i]'(eq ▸ h)))
      (Array.mapIdxM as f) := by
  let rec go {bs i j h} (h₁ : j = bs.size) (h₂ : ∀ i h h', p ⟨i, h⟩ bs[i]) (hm : motive j) :
    SatisfiesM
      (fun arr => motive as.size ∧ ∃ eq : arr.size = as.size, ∀ i h, p ⟨i, h⟩ (arr[i]'(eq ▸ h)))
      (Array.mapIdxM.map as f i j h bs) := by
    induction i generalizing j bs with simp [mapIdxM.map]
    | zero =>
      have := (Nat.zero_add _).symm.trans h
      exact .pure ⟨this ▸ hm, h₁ ▸ this, fun _ _ => h₂ ..⟩
    | succ i ih =>
      refine (hs _ (by exact hm)).bind fun b hb => ih (by simp [h₁]) (fun i hi hi' => ?_) hb.2
      simp at hi'; simp [get_push]; split
      · next h => exact h₂ _ _ h
      · next h => cases h₁.symm ▸ (Nat.le_or_eq_of_le_succ hi').resolve_left h; exact hb.1
  simp [mapIdxM]; exact go rfl nofun h0

theorem mapIdx_induction (as : Array α) (f : Fin as.size → α → β)
    (motive : Nat → Prop) (h0 : motive 0)
    (p : Fin as.size → β → Prop)
    (hs : ∀ i, motive i.1 → p i (f i as[i]) ∧ motive (i + 1)) :
    motive as.size ∧ ∃ eq : (Array.mapIdx as f).size = as.size,
      ∀ i h, p ⟨i, h⟩ ((Array.mapIdx as f)[i]'(eq ▸ h)) := by
  have := SatisfiesM_mapIdxM (m := Id) (as := as) (f := f) motive h0
  simp [SatisfiesM_Id_eq] at this
  exact this _ hs

theorem mapIdx_induction' (as : Array α) (f : Fin as.size → α → β)
    (p : Fin as.size → β → Prop) (hs : ∀ i, p i (f i as[i])) :
    ∃ eq : (Array.mapIdx as f).size = as.size,
      ∀ i h, p ⟨i, h⟩ ((Array.mapIdx as f)[i]'(eq ▸ h)) :=
  (mapIdx_induction _ _ (fun _ => True) trivial p fun _ _ => ⟨hs .., trivial⟩).2

@[simp] theorem size_mapIdx (a : Array α) (f : Fin a.size → α → β) : (a.mapIdx f).size = a.size :=
  (mapIdx_induction' (p := fun _ _ => True) (hs := fun _ => trivial)).1

@[simp] theorem getElem_mapIdx (a : Array α) (f : Fin a.size → α → β) (i : Nat) (h) :
    haveI : i < a.size := by simp_all
    (a.mapIdx f)[i]'h = f ⟨i, this⟩ a[i] :=
  (mapIdx_induction' _ _ (fun i b => b = f i a[i]) fun _ => rfl).2 i _

theorem size_modifyM [Monad m] [LawfulMonad m] (a : Array α) (i : Nat) (f : α → m α) :
    SatisfiesM (·.size = a.size) (a.modifyM i f) := by
  unfold modifyM; split
  · exact .bind_pre <| .of_true fun _ => .pure <| by simp only [size_set]
  · exact .pure rfl

@[simp] theorem size_modify (a : Array α) (i : Nat) (f : α → α) : (a.modify i f).size = a.size := by
  rw [← SatisfiesM_Id_eq (p := (·.size = a.size)) (x := a.modify i f)]
  apply size_modifyM

@[simp] theorem size_zipWithIndex (as : Array α) : as.zipWithIndex.size = as.size :=
  Array.size_mapIdx _ _

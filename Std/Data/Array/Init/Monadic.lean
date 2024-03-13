/-
Copyright (c) 2022 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Std.Data.Bool
import Std.Classes.SatisfiesM

/-!
# Lemmas about monadic functions on `Array`, in terms of the `SatisfiesM` predicate.

These lemmas are used in `Std.Data.HashMap.Basic`,
and so are in the `Std.Data.Array.Init` directory.
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
      (fun arr => motive as.size ∧ ∃ eq : arr.size = as.size, ∀ i h, p ⟨i, h⟩ (arr[i]'(eq ▸ h)))
      (Array.mapM f as) := by
  rw [mapM_eq_foldlM]
  refine SatisfiesM_foldlM (m := m) (β := Array β)
    (motive := fun i arr => motive i ∧ arr.size = i ∧ ∀ i h2, p i (arr[i.1]'h2)) ?z ?s
    |>.imp fun ⟨h₁, eq, h₂⟩ => ⟨h₁, eq, fun _ _ => h₂ ..⟩
  · case z => exact ⟨h0, rfl, nofun⟩
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

/-
Copyright (c) 2022 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Std.Data.Bool
import Std.Data.Array.Init.Monad

/-!
## Bootstrapping theorems about arrays

This file contains some theorems about `Array` and `List` needed for `Std.List.Basic`.
-/

namespace Array

-- This proof is the pure version of `Array.SatisfiesM_foldlM`,
-- reproduced to avoid a dependency on `SatisfiesM`.
theorem foldl_induction
    {as : Array α} (motive : Nat → β → Prop) {init : β} (h0 : motive 0 init) {f : β → α → β}
    (hf : ∀ i : Fin as.size, ∀ b, motive i.1 b → motive (i.1 + 1) (f b as[i])) :
    motive as.size (as.foldl f init) := by
  let rec go {i j b} (h₁ : j ≤ as.size) (h₂ : as.size ≤ i + j) (H : motive j b) :
    (motive as.size) (foldlM.loop (m := Id) f as as.size (Nat.le_refl _) i j b) := by
    unfold foldlM.loop; split
    · next hj =>
      split
      · cases Nat.not_le_of_gt (by simp [hj]) h₂
      · exact go hj (by rwa [Nat.succ_add] at h₂) (hf ⟨j, hj⟩ b H)
    · next hj => exact Nat.le_antisymm h₁ (Nat.ge_of_not_lt hj) ▸ H
  simpa [foldl, foldlM] using go (Nat.zero_le _) (Nat.le_refl _) h0

-- Auxiliary for `any_iff_exists`.
theorem anyM_loop_iff_exists (p : α → Bool) (as : Array α) (start stop) (h : stop ≤ as.size) :
    anyM.loop (m := Id) p as stop h start = true ↔
      ∃ i : Fin as.size, start ≤ ↑i ∧ ↑i < stop ∧ p as[i] = true := by
  unfold anyM.loop
  split <;> rename_i h₁
  · dsimp
    split <;> rename_i h₂
    · simp only [true_iff]
      refine ⟨⟨start, by omega⟩, by dsimp; omega, by dsimp; omega, h₂⟩
    · rw [anyM_loop_iff_exists]
      constructor
      · rintro ⟨i, ge, lt, h⟩
        have : start ≠ i := by rintro rfl; omega
        exact ⟨i, by omega, lt, h⟩
      · rintro ⟨i, ge, lt, h⟩
        have : start ≠ i := by rintro rfl; erw [h] at h₂; simp_all
        exact ⟨i, by omega, lt, h⟩
  · simp
    omega
termination_by stop - start

-- This could also be proved from `SatisfiesM_anyM_iff_exists` in `Std.Data.Array.Init.Monad`
theorem any_iff_exists (p : α → Bool) (as : Array α) (start stop) :
    any as p start stop ↔ ∃ i : Fin as.size, start ≤ i.1 ∧ i.1 < stop ∧ p as[i] := by
  dsimp [any, anyM, Id.run]
  split
  · rw [anyM_loop_iff_exists]
  · rw [anyM_loop_iff_exists]
    constructor
    · rintro ⟨i, ge, _, h⟩
      exact ⟨i, by omega, by omega, h⟩
    · rintro ⟨i, ge, _, h⟩
      exact ⟨i, by omega, by omega, h⟩

theorem any_eq_true (p : α → Bool) (as : Array α) :
    any as p ↔ ∃ i : Fin as.size, p as[i] := by simp [any_iff_exists, Fin.isLt]

theorem any_def {p : α → Bool} (as : Array α) : as.any p = as.data.any p := by
  rw [Bool.eq_iff_iff, any_eq_true, List.any_eq_true]; simp only [List.mem_iff_get]
  exact ⟨fun ⟨i, h⟩ => ⟨_, ⟨i, rfl⟩, h⟩, fun ⟨_, ⟨i, rfl⟩, h⟩ => ⟨i, h⟩⟩

theorem contains_def [DecidableEq α] {a : α} {as : Array α} : as.contains a ↔ a ∈ as := by
  rw [mem_def, contains, any_def, List.any_eq_true]; simp [and_comm]

instance [DecidableEq α] (a : α) (as : Array α) : Decidable (a ∈ as) :=
  decidable_of_iff _ contains_def

theorem map_eq_foldl (as : Array α) (f : α → β) :
    as.map f = as.foldl (fun r a => r.push (f a)) #[] := by
  dsimp [map, mapM, Id.run]
  unfold mapM.map
  split
  · simp
    sorry
  · sorry


theorem map_spec (as : Array α) (f : α → β) (motive : Nat → Prop) (h0 : motive 0)
    (p : Fin as.size → β → Prop) (hs : ∀ i, motive i.1 → p i (f as[i]) ∧ motive (i+1)) :
    motive as.size ∧
      ∃ eq : (as.map f).size = as.size, ∀ i h, p ⟨i, h⟩ ((as.map f)[i]'(eq ▸ h)) := by
  have t := foldl_induction (as := as) (β := Array β)
    (motive := fun i arr => motive i ∧ arr.size = i ∧ ∀ i h2, p i (arr[i.1]'h2))
    (init := #[]) (f := fun r a => r.push (f a)) ?_ ?_
  obtain ⟨m, eq, w⟩ := t
  · refine ⟨m, by simpa [map_eq_foldl] using eq, ?_⟩
    intro i h
    simp [eq] at w
    specialize w ⟨i, h⟩ trivial
    simpa [map_eq_foldl] using w
  · exact ⟨h0, rfl, nofun⟩
  · intro i b ⟨m, ⟨eq, w⟩⟩
    refine ⟨?_, ?_, ?_⟩
    · exact (hs _ m).2
    · simp_all
    · intro j h
      simp at h ⊢
      by_cases h' : j < size b
      · rw [get_push]
        simp_all
      · rw [get_push, dif_neg h']
        simp only [show j = i by omega]
        exact (hs _ m).1

theorem map_spec' (as : Array α) (f : α → β) (p : Fin as.size → β → Prop)
    (hs : ∀ i, p i (f as[i])) :
    ∃ eq : (as.map f).size = as.size, ∀ i h, p ⟨i, h⟩ ((as.map f)[i]'(eq ▸ h)) := by
  simpa using map_spec as f (fun _ => True) trivial p (by simp_all)

-- theorem SatisfiesM_mapM [Monad m] [LawfulMonad m] (as : Array α) (f : α → m β)
--     (motive : Nat → Prop) (h0 : motive 0)
--     (p : Fin as.size → β → Prop)
--     (hs : ∀ i, motive i.1 → SatisfiesM (p i · ∧ motive (i + 1)) (f as[i])) :
--     SatisfiesM
--       (fun arr => motive as.size ∧ ∃ eq : arr.size = as.size, ∀ i h, p ⟨i, h⟩ (arr[i]'(eq ▸ h)))
--       (Array.mapM f as) := by
--   rw [mapM_eq_foldlM]
--   refine SatisfiesM_foldlM (m := m) (β := Array β)
--     (motive := fun i arr => motive i ∧ arr.size = i ∧ ∀ i h2, p i (arr[i.1]'h2)) ?z ?s
--     |>.imp fun ⟨h₁, eq, h₂⟩ => ⟨h₁, eq, fun _ _ => h₂ ..⟩
--   · case z => exact ⟨h0, rfl, nofun⟩
--   · case s =>
--     intro ⟨i, hi⟩ arr ⟨ih₁, eq, ih₂⟩
--     refine (hs _ ih₁).map fun ⟨h₁, h₂⟩ => ⟨h₂, by simp [eq], fun j hj => ?_⟩
--     simp [get_push] at hj ⊢; split; {apply ih₂}
--     cases j; cases (Nat.le_or_eq_of_le_succ hj).resolve_left ‹_›; cases eq; exact h₁

-- theorem SatisfiesM_mapM' [Monad m] [LawfulMonad m] (as : Array α) (f : α → m β)
--     (p : Fin as.size → β → Prop)
--     (hs : ∀ i, SatisfiesM (p i) (f as[i])) :
--     SatisfiesM
--       (fun arr => ∃ eq : arr.size = as.size, ∀ i h, p ⟨i, h⟩ (arr[i]'(eq ▸ h)))
--       (Array.mapM f as) :=
--   (SatisfiesM_mapM _ _ (fun _ => True) trivial _ (fun _ h => (hs _).imp (⟨·, h⟩))).imp (·.2)

/-
Copyright (c) 2021 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Mario Carneiro, Gabriel Ebner
-/
module

public import Batteries.Classes.SatisfiesM
public import Batteries.Util.ProofWanted
public import Std.Tactic.Do
import Batteries.Data.List.Monadic
import all Init.Data.Array.Basic  -- for unfolding `modifyM`

@[expose] public section
namespace Std.Do
set_option mvcgen.warning false

@[spec]
theorem Spec.mapM_array {α β : Type w} [Monad m] [LawfulMonad m] [WPMonad m ps]
    {xs : Array α} {f : α → m β}
    (inv : Invariant xs.toList (Array β) ps)
    (step : ∀ pref cur suff (h : xs.toList = pref ++ cur :: suff) acc,
      ⦃inv.1 (⟨pref, cur::suff, h.symm⟩, acc)⦄
        f cur
      ⦃(fun b => inv.1 (⟨pref ++ [cur], suff, by simp [h]⟩, acc.push b), inv.2)⦄) :
    ⦃inv.1 (⟨[], xs.toList, rfl⟩, #[])⦄
    xs.mapM f
    ⦃(fun bs => inv.1 (⟨xs.toList, [], by simp⟩, bs), inv.2)⦄ := by
  rw [Array.mapM_eq_foldlM]
  mvcgen
  invariants
    · inv
  apply step (h := ‹_›)

@[spec]
theorem Spec.anyM_array [Monad m] [LawfulMonad m] [WPMonad m ps]
    {xs : Array α} {p : α → m Bool}
    {tru : Assertion ps}
    {fal : xs.toList.Cursor → Assertion ps}
    (h0 : ⊢ₛ fal ⟨[], xs.toList, rfl⟩)
    (hp : ∀ pref cur suff (h : xs.toList = pref ++ cur :: suff),
      ⦃fal ⟨pref, cur::suff, h.symm⟩⦄
        p cur
      ⦃⇓ b => if b then tru else fal ⟨pref ++ [cur], suff, by simp [h]⟩⦄) :
    ⦃⌜True⌝⦄
    xs.anyM p
    ⦃⇓ res => if res then tru else fal ⟨xs.toList, [], by simp⟩⦄ := by
  rw [← Array.anyM_toList]
  exact Spec.anyM_list h0 hp

@[spec]
theorem Spec.mapFinIdxM_array [Monad m] [LawfulMonad m] [WPMonad m ps]
    {xs : Array α} {f : (i : Nat) → α → i < xs.size → m β}
    {motive : Nat → Prop}
    {p : (i : Nat) → β → i < xs.size → Prop}
    (h0 : motive 0)
    (hs : ∀ i (h : i < xs.size), motive i →
      ⦃⌜True⌝⦄ f i xs[i] h ⦃⇓ b => ⌜p i b h ∧ motive (i + 1)⌝⦄) :
    ⦃⌜True⌝⦄
    xs.toList.mapFinIdxM f
    ⦃⇓ bs => ⌜motive xs.toList.length ∧ ∃ eq : bs.length = xs.toList.length, ∀ i h, p i bs[i] h⌝⦄ := by
  simp only [← Array.getElem_toList] at *
  simp only [← Array.length_toList] at *
  rw [List.mapFinIdxM_toArray, map_eq_pure_bind, bind_pure_comp]
  have hinner := Spec.mapFinIdxM_list h0 hs
  skip




end Std.Do

/-!
# Results about monadic operations on `Array`, in terms of `SatisfiesM`.

The pure versions of these theorems are proved in `Batteries.Data.Array.Lemmas` directly,
in order to minimize dependence on `SatisfiesM`.
-/

namespace Array
set_option mvcgen.warning false
open Std.Do

theorem size_mapM {α β : Type u} [Monad m] [LawfulMonad m] [WPMonad m ps]
    {xs : Array α} {f : α → m β}
    (hf : ∀ x, ⦃⌜True⌝⦄ f x ⦃⇓ _ => ⌜True⌝⦄) :
    ⦃⌜True⌝⦄
    xs.mapM f
    ⦃⇓ bs => ⌜bs.size = xs.size⌝⦄ := by
  rw [Array.mapM_eq_foldlM]
  mvcgen
  invariants
    · ⇓⟨cursor, acc⟩ => ⌜acc.size = cursor.prefix.length⌝
  . mspec hf
    simp_all
  . simp

theorem anyM_iff_exists [Monad m] [LawfulMonad m] [WPMonad m ps]
    {xs : Array α} {p : α → m Bool} {q : xs.toList.Cursor → Prop}
    (hp : ∀ pref cur suff (h : xs.toList = pref ++ cur :: suff),
      ⦃⌜True⌝⦄ p cur ⦃⇓ b => ⌜b = true ↔ q ⟨pref, cur::suff, h.symm⟩⌝⦄) :
    ⦃⌜True⌝⦄
    xs.anyM p
    ⦃⇓ res => ⌜res = true ↔ ∃ cursor : xs.toList.Cursor, cursor.suffix ≠ [] ∧ q cursor⌝⦄ := by
  rw [← Array.anyM_toList]
  apply List.anyM_iff_exists hp


theorem SatisfiesM_mapFinIdxM [Monad m] [LawfulMonad m]
    {as : Array α} {f : (i : Nat) → α → i < as.size → m β} {motive : Nat → Prop}
    {p : (i : Nat) → β → i < as.size → Prop}
    (h0 : motive 0) (hs : ∀ i h, motive i → SatisfiesM (p i · h ∧ motive (i + 1)) (f i as[i] h)) :
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

theorem SatisfiesM_mapIdxM [Monad m] [LawfulMonad m] {as : Array α} {f : Nat → α → m β}
    {p : (i : Nat) → β → i < as.size → Prop} {motive : Nat → Prop}
    (h0 : motive 0) (hs : ∀ i h, motive i → SatisfiesM (p i · h ∧ motive (i + 1)) (f i as[i])) :
    SatisfiesM
      (fun arr => motive as.size ∧ ∃ eq : arr.size = as.size, ∀ i h, p i arr[i] h)
      (as.mapIdxM f) :=
  SatisfiesM_mapFinIdxM h0 hs

theorem size_mapFinIdxM [Monad m] [LawfulMonad m]
    (as : Array α) (f : (i : Nat) → α → i < as.size → m β) :
    SatisfiesM (fun arr => arr.size = as.size) (Array.mapFinIdxM as f) :=
  (SatisfiesM_mapFinIdxM (motive := fun _ => True) trivial
    (fun _ _ _ => .of_true fun _ => ⟨trivial, trivial⟩)).imp (·.2.1)

theorem size_mapIdxM [Monad m] [LawfulMonad m] (as : Array α) (f : Nat → α → m β) :
    SatisfiesM (fun arr => arr.size = as.size) (Array.mapIdxM f as) :=
  size_mapFinIdxM _ _

theorem size_modifyM [Monad m] [LawfulMonad m] (as : Array α) (i : Nat) (f : α → m α) :
    SatisfiesM (·.size = as.size) (as.modifyM i f) := by
  unfold modifyM; split
  · exact .bind_pre <| .of_true fun _ => .pure <| by simp only [size_set]
  · exact .pure rfl

end Array

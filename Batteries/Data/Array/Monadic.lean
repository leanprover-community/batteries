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

theorem SatisfiesM_anyM [Monad m] [LawfulMonad m] {p : α → m Bool} {as : Array α}
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
    {p : α → m Bool} {as : Array α} {q : Fin as.size → Prop}
    (hp : ∀ i : Fin as.size, start ≤ i.1 → i.1 < stop → SatisfiesM (· = true ↔ q i) (p as[i])) :
    SatisfiesM
      (fun res => res = true ↔ ∃ i : Fin as.size, start ≤ i.1 ∧ i.1 < stop ∧ q i)
      (anyM p as start stop) := by
  cases Nat.le_total start (min stop as.size) with
  | inl hstart =>
    refine (SatisfiesM_anyM hstart
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
    {as : Array α} {init : β} {motive : Nat → β → Prop} {f : α → β → m β}
    (h0 : motive as.size init)
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

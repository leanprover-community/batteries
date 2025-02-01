/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Batteries.Util.ProofWanted
import Batteries.Classes.SatisfiesM
import Batteries.Data.Array.Monadic

namespace Vector

theorem toArray_mapM [Monad m] [LawfulMonad m] (a : Vector α n) (f : α → m β) :
    toArray <$> a.mapM f = a.toArray.mapM f := by
  let rec go (i : Nat) (h : i ≤ n) (acc : Vector β i) :
      toArray <$> mapM.go f a i h acc = Array.mapM.map f a.toArray i acc.toArray := by
    unfold mapM.go Array.mapM.map; simp only [size_toArray, getElem_toArray]
    split
    · simp only [map_bind]
      conv => lhs; arg 2; intro; rw [go]
      rfl
    · simp only [map_pure, toArray_cast]
  simp only [mapM, Array.mapM]
  exact go _ _ _

theorem toArray_mapFinIdxM [Monad m] [LawfulMonad m]
    (a : Vector α n) (f : (i : Nat) → α → (h : i < n) → m β) :
    toArray <$> a.mapFinIdxM f = a.toArray.mapFinIdxM (fun i x h => f i x (size_toArray a ▸ h)) := by
  let rec go (i j : Nat) (inv : i + j = n) (bs : Vector β (n - i)) :
      toArray <$> mapFinIdxM.map a f i j inv bs
      = Array.mapFinIdxM.map a.toArray (fun i x h => f i x (size_toArray a ▸ h))
        i j (size_toArray _ ▸ inv) bs.toArray := by
    match i with
    | 0 => simp only [mapFinIdxM.map, map_pure, Array.mapFinIdxM.map, Nat.sub_zero]
    | k + 1 =>
      simp only [mapFinIdxM.map, map_bind, Array.mapFinIdxM.map, getElem_toArray]
      conv => lhs; arg 2; intro; rw [go]
      rfl
  simp only [mapFinIdxM, Array.mapFinIdxM, size_toArray]
  exact go _ _ _ _

theorem toArray_mapIdxM [Monad m] [LawfulMonad m] (a : Vector α n) (f : Nat → α → m β) :
    toArray <$> a.mapIdxM f = a.toArray.mapIdxM f := by
  exact toArray_mapFinIdxM _ _

theorem _root_.LawfulFunctor.map_inj_right_of_nonempty [Functor f] [LawfulFunctor f] [Nonempty α]
    {g : α → β} (h : ∀ {x y : α}, g x = g y → x = y) {x y : f α} :
    g <$> x = g <$> y ↔ x = y := by
  constructor
  · open Classical in
    let g' a := if h : ∃ b, g b = a then h.choose else Classical.ofNonempty
    have g'g a : g' (g a) = a := by
      simp only [exists_apply_eq_apply, ↓reduceDIte, g']
      exact h (_ : ∃ b, g b = g a).choose_spec
    intro h'
    simpa only [Functor.map_map, g'g, id_map'] using congrArg (g' <$> ·) h'
  · intro h'
    rw [h']

theorem _root_.LawfulMonad.map_inj_right [Monad m] [LawfulMonad m]
    {f : α → β} (h : ∀ {x y : α}, f x = f y → x = y) {x y : m α} :
    f <$> x = f <$> y ↔ x = y := by
  by_cases hempty : Nonempty α
  · exact LawfulFunctor.map_inj_right_of_nonempty h
  · constructor
    · intro h'
      have (x : m α) : x = (do let a ← x; let b ← pure (f a); x) := by
        conv => lhs; rw [← bind_pure x]
        congr; funext a
        exact (hempty ⟨a⟩).elim
      rw [this x, this y]
      rw [map_eq_pure_bind, map_eq_pure_bind] at h'
      rw [← bind_assoc, h', bind_assoc]
      congr; funext a
      exact (hempty ⟨a⟩).elim
    · intro h'
      rw [h']

theorem mapM_mk [Monad m] [LawfulMonad m] [MonadSatisfying m]
    (a : Array α) (h : a.size = n) (f : α → m β) :
    (Vector.mk a h).mapM f =
      (fun ⟨a, h'⟩ => Vector.mk a (h'.trans h)) <$> satisfying (Array.size_mapM f a) := by
  rw [← LawfulMonad.map_inj_right Vector.toArray_inj.mp]
  simp only [Functor.map_map, MonadSatisfying.val_eq, toArray_mapM]

theorem mapIdxM_mk [Monad m] [LawfulMonad m] [MonadSatisfying m]
    (a : Array α) (h : a.size = n) (f : Nat → α → m β) :
    (Vector.mk a h).mapIdxM f =
      (fun ⟨a, h'⟩ => Vector.mk a (h'.trans h)) <$> satisfying (Array.size_mapIdxM a f) := by
  rw [← LawfulMonad.map_inj_right Vector.toArray_inj.mp]
  simp only [Functor.map_map, MonadSatisfying.val_eq, toArray_mapIdxM]

theorem mapFinIdxM_mk [Monad m] [LawfulMonad m] [MonadSatisfying m]
    (a : Array α) (h : a.size = n) (f : (i : Nat) → α → (h : i < n) → m β) :
    (Vector.mk a h).mapFinIdxM f =
      (fun ⟨a, h'⟩ => Vector.mk a (h'.trans h)) <$> satisfying
        (Array.size_mapFinIdxM a (fun i a h' => f i a (h ▸ h'))) := by
  rw [← LawfulMonad.map_inj_right Vector.toArray_inj.mp]
  simp only [Functor.map_map, MonadSatisfying.val_eq, toArray_mapFinIdxM]

end Vector

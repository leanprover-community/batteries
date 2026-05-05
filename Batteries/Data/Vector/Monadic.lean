/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Batteries.Classes.SatisfiesM
public import Batteries.Data.Array.Monadic

@[expose] public section

set_option linter.deprecated false

/-!
**Deprecated (since 2026-05-05):** the entire `SatisfiesM`/`MonadSatisfying` API is unused
downstream. The content of these `mk`-form lemmas is subsumed by the upstream
`Vector.toArray_mapM`, `Vector.toArray_mapIdxM`, and `Vector.toArray_mapFinIdxM` lemmas
in `Init.Data.Vector.Lemmas`/`Init.Data.Vector.MapIdx`, which characterize the same
monadic operations without requiring `MonadSatisfying`.
-/

namespace Vector

@[deprecated Vector.toArray_mapM (since := "2026-05-05")]
theorem mapM_mk [Monad m] [LawfulMonad m] [MonadSatisfying m]
    (a : Array α) (h : a.size = n) (f : α → m β) :
    (Vector.mk a h).mapM f =
      (fun ⟨a, h'⟩ => Vector.mk a (h'.trans h)) <$> satisfying (Array.size_mapM f a) := by
  rw [← _root_.map_inj_right Vector.toArray_inj.mp]
  simp only [Functor.map_map, MonadSatisfying.val_eq, toArray_mapM]

@[deprecated Vector.toArray_mapIdxM (since := "2026-05-05")]
theorem mapIdxM_mk [Monad m] [LawfulMonad m] [MonadSatisfying m]
    (a : Array α) (h : a.size = n) (f : Nat → α → m β) :
    (Vector.mk a h).mapIdxM f =
      (fun ⟨a, h'⟩ => Vector.mk a (h'.trans h)) <$> satisfying (Array.size_mapIdxM a f) := by
  rw [← _root_.map_inj_right Vector.toArray_inj.mp]
  simp only [Functor.map_map, MonadSatisfying.val_eq, toArray_mapIdxM]

@[deprecated Vector.toArray_mapFinIdxM (since := "2026-05-05")]
theorem mapFinIdxM_mk [Monad m] [LawfulMonad m] [MonadSatisfying m]
    (a : Array α) (h : a.size = n) (f : (i : Nat) → α → (h : i < n) → m β) :
    (Vector.mk a h).mapFinIdxM f =
      (fun ⟨a, h'⟩ => Vector.mk a (h'.trans h)) <$> satisfying
        (Array.size_mapFinIdxM a (fun i a h' => f i a (h ▸ h'))) := by
  rw [← _root_.map_inj_right Vector.toArray_inj.mp]
  simp only [Functor.map_map, MonadSatisfying.val_eq, toArray_mapFinIdxM]

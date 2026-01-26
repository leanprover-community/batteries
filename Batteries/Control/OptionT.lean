/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich
-/
module

public import Batteries.Control.LawfulMonadState
import all Init.Control.Option

@[expose] public section

/-!
# Lemmas About Option Monad Transformer

This file contains lemmas about the behavior of `OptionT` and `OptionT.run`.
-/

namespace OptionT

@[simp] theorem run_monadLift [Monad m] [LawfulMonad m] [MonadLiftT n m] (x : n α) :
    (monadLift x : OptionT m α).run = some <$> (monadLift x : m α) := (map_eq_pure_bind _ _).symm

@[simp] theorem run_mapConst [Monad m] [LawfulMonad m] (x : OptionT m α) (y : β) :
    (Functor.mapConst y x).run = Option.map (Function.const α y) <$> x.run := run_map _ _

instance [Monad m] [LawfulMonad m] [MonadStateOf σ m] [LawfulMonadStateOf σ m] :
    LawfulMonadStateOf σ (OptionT m) where
  modifyGet_eq f := by simp [← liftM_modifyGet, ← liftM_get, LawfulMonadStateOf.modifyGet_eq]
  get_bind_const mx := OptionT.ext (by simp [← liftM_get])
  get_bind_get_bind mx := OptionT.ext (by simp [← liftM_get])
  get_bind_set_bind mx := OptionT.ext (by simp [← liftM_get, ← liftM_set])
  set_bind_get s := OptionT.ext (by simp [← liftM_get, ← liftM_set])
  set_bind_set s s' := OptionT.ext (by simp [← liftM_set])

end OptionT

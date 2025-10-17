/-
Copyright (c) 2025 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import Lean.Elab.Command
import all Lean.CoreM  -- for unfolding `liftIOCore`
import all Init.System.IO  -- for unfolding `BaseIO.toEIO`
import all Init.Control.StateRef  -- for unfolding `StateRefT'.lift`

@[expose] public section

/-!
# Lawful instances of `MonadLift` for the Lean monad stack.
-/

open Lean Elab Term Tactic Command

instance : LawfulMonadLift BaseIO (EIO ε) where
  monadLift_pure _ := rfl
  monadLift_bind ma f := by
    simp only [MonadLift.monadLift, bind]
    unfold BaseIO.toEIO EStateM.bind IO.RealWorld
    simp only
    funext x
    rcases ma x with a | a
    · simp only
    · contradiction

instance : LawfulMonadLift (ST σ) (EST ε σ) where
  monadLift_pure a := rfl
  monadLift_bind ma f := by
    simp only [MonadLift.monadLift, bind]
    unfold EStateM.bind
    simp only
    funext x
    rcases ma x with a | a
    · simp only
    · contradiction

instance : LawfulMonadLift IO CoreM where
  monadLift_pure _ := rfl
  monadLift_bind ma f := by
    simp only [MonadLift.monadLift, bind, pure, Core.liftIOCore, liftM, monadLift, getRef, read,
      readThe, MonadReaderOf.read, IO.toEIO]
    unfold StateRefT'.lift ReaderT.read ReaderT.bind ReaderT.pure
    simp only [Function.comp_apply, bind, pure]
    unfold ReaderT.bind ReaderT.pure
    simp only [bind, pure]
    unfold EStateM.adaptExcept EStateM.bind EStateM.pure
    simp only
    funext _ _ s
    rcases ma s with a | a <;> simp only

instance : LawfulMonadLiftT (EIO Exception) CommandElabM := inferInstance
instance : LawfulMonadLiftT (EIO Exception) CoreM := inferInstance
instance : LawfulMonadLiftT CoreM MetaM := inferInstance
instance : LawfulMonadLiftT MetaM TermElabM := inferInstance
instance : LawfulMonadLiftT TermElabM TacticM := inferInstance

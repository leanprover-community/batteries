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
import all Init.System.ST

@[expose] public section

/-!
# Lawful instances of `MonadLift` for the Lean monad stack.
-/

open Lean Elab Term Tactic Command

instance : LawfulMonadLift (ST σ) (EST ε σ) where
  monadLift_pure _ := rfl
  monadLift_bind _ _ := rfl

instance : LawfulMonadLift BaseIO (EIO ε) :=
  inferInstanceAs <| LawfulMonadLift (ST IO.RealWorld) (EST ε IO.RealWorld)

/-! ### `EIO.adapt` simp lemmas -/

@[simp] theorem EIO.adapt_pure (f : ε₁ → ε₂) (a : α) :
    EIO.adapt f (pure a : EIO ε₁ α) = (pure a : EIO ε₂ α) := by rfl

private theorem EIO.bind_eq_EST_bind (ma : EIO ε α) (f : α → EIO ε β) :
    (ma >>= f) = EST.bind ma f := by rfl

private theorem EIO.adapt_EST_bind (f : ε₁ → ε₂) (ma : EIO ε₁ α) (g : α → EIO ε₁ β) :
    EIO.adapt f (EST.bind ma g) = EST.bind (EIO.adapt f ma) (fun a => EIO.adapt f (g a)) := by
  funext s; simp only [EIO.adapt, EST.bind]; cases ma s <;> rfl

@[simp] theorem EIO.adapt_bind (f : ε₁ → ε₂) (ma : EIO ε₁ α) (g : α → EIO ε₁ β) :
    EIO.adapt f (ma >>= g) = EIO.adapt f ma >>= fun a => EIO.adapt f (g a) := by
  simp only [EIO.bind_eq_EST_bind, EIO.adapt_EST_bind]

/-! ### `StateRefT'.lift` simp lemmas -/

@[simp] theorem StateRefT'.lift_pure [Monad m] (a : α) :
    (StateRefT'.lift (pure a) : StateRefT' ω σ m α) = pure a := by rfl

@[simp] theorem StateRefT'.lift_bind [Monad m] (ma : m α) (f : α → m β) :
    (StateRefT'.lift (ma >>= f) : StateRefT' ω σ m β) =
      StateRefT'.lift ma >>= fun a => StateRefT'.lift (f a) := by rfl

/-! ### `LawfulMonadLift IO CoreM` -/

private theorem Core.run_liftIOCore (x : IO α) (r : Core.Context) :
    ReaderT.run (Core.liftIOCore x) r =
      (StateRefT'.lift
        (EIO.adapt
          (fun err => Exception.error r.ref (MessageData.ofFormat (format (toString err)))) x) :
        StateRefT' IO.RealWorld Core.State (EIO Exception) α) := by rfl

instance : LawfulMonadLift IO CoreM where
  monadLift_pure a := by
    ext r
    simp [MonadLift.monadLift, Core.run_liftIOCore]
  monadLift_bind ma f := by
    ext r
    simp [MonadLift.monadLift, Core.run_liftIOCore]

instance : LawfulMonadLiftT (EIO Exception) CommandElabM := inferInstance
instance : LawfulMonadLiftT (EIO Exception) CoreM := inferInstance
instance : LawfulMonadLiftT CoreM MetaM := inferInstance
instance : LawfulMonadLiftT MetaM TermElabM := inferInstance
instance : LawfulMonadLiftT TermElabM TacticM := inferInstance

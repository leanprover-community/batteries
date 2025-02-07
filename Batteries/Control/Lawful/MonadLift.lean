/-
Copyright (c) 2025 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

/-!
# Lawful version of `MonadLift`

This file defines the `LawfulMonadLift(T)` class, which adds laws to the `MonadLift(T)` class.
-/

universe u v w

/-- The `MonadLift` typeclass only contains the lifting operation. `LawfulMonadLift` further
  asserts that lifting commutes with `pure` and `bind`:
```
monadLift (pure a) = pure a
monadLift ma >>= monadLift ∘ f = monadLift (ma >>= f)
```
-/
class LawfulMonadLift (m : semiOutParam (Type u → Type v)) (n : Type u → Type w)
    [Monad m] [Monad n] [MonadLift m n] : Prop where

  /-- Lifting preserves `pure` -/
  monadLift_pure {α : Type u} (a : α) : @MonadLift.monadLift m n _ _ (pure a) = pure a

  /-- Lifting preserves `bind` -/
  monadLift_bind {α β : Type u} (ma : m α) (f : α → m β) :
    MonadLift.monadLift ma >>= MonadLift.monadLift ∘ f =
      MonadLift.monadLift (n := n) (ma >>= f)

/-- The `MonadLiftT` typeclass only contains the transitive lifting operation.
  `LawfulMonadLiftT` further asserts that lifting commutes with `pure` and `bind`:
```
monadLift (pure a) = pure a
monadLift ma >>= monadLift ∘ f = monadLift (ma >>= f)
```
-/
class LawfulMonadLiftT (m : Type u → Type v) (n : Type u → Type w) [Monad m] [Monad n]
    [MonadLiftT m n] : Prop where

  /-- Lifting preserves `pure` -/
  monadLift_pure {α : Type u} (a : α) : @monadLift m n _ _ (pure a) = pure a

  /-- Lifting preserves `bind` -/
  monadLift_bind {α β : Type u} (ma : m α) (f : α → m β) :
    monadLift ma >>= monadLift ∘ f = monadLift (n := n) (ma >>= f)

export LawfulMonadLiftT (monadLift_pure monadLift_bind)

@[simp]
theorem liftM_pure {m : Type u → Type v} {n : Type u → Type w} [Monad m] [Monad n] [MonadLiftT m n]
    [LawfulMonadLiftT m n] {α : Type u} (a : α) : liftM (pure a : m α) = pure (f := n) a :=
  monadLift_pure _

@[simp]
theorem liftM_bind {m : Type u → Type v} {n : Type u → Type w} [Monad m] [Monad n] [MonadLiftT m n]
    [LawfulMonadLiftT m n] {α β : Type u} (ma : m α) (f : α → m β) :
      liftM ma >>= (fun a => liftM (f a)) = liftM (n := n) (ma >>= f) :=
  monadLift_bind _ _

instance {m : semiOutParam (Type u → Type v)} {n : Type u → Type w} [Monad m] [Monad n]
    [MonadLift m n] [LawfulMonadLift m n] : LawfulMonadLiftT m n where
  monadLift_pure := LawfulMonadLift.monadLift_pure
  monadLift_bind := LawfulMonadLift.monadLift_bind

namespace StateT

variable {σ : Type u} {m : Type u → Type v} [Monad m] [LawfulMonad m]

instance : LawfulMonadLift m (StateT σ m) where
  monadLift_pure := by
    intro α a
    simp only [MonadLift.monadLift]
    unfold StateT.lift StateT.instMonad StateT.bind StateT.pure
    simp only [bind_pure_comp, map_pure]
  monadLift_bind := by
    intro α β ma f
    simp only [MonadLift.monadLift]
    unfold StateT.lift StateT.instMonad StateT.bind StateT.pure
    simp only [bind_pure_comp, Function.comp_apply, bind_map_left, map_bind]

end StateT

namespace ReaderT

variable {ρ : Type u} {m : Type u → Type v} [Monad m]

instance : LawfulMonadLift m (ReaderT ρ m) where
  monadLift_pure := by
    intro α a
    funext x
    simp only [MonadLift.monadLift, pure, ReaderT.pure]
  monadLift_bind := by
    intro α β ma f
    funext x
    simp only [bind, ReaderT.bind, MonadLift.monadLift, Function.comp_apply]

end ReaderT

namespace OptionT

variable {m : Type u → Type v} [Monad m] [LawfulMonad m]

@[simp]
theorem lift_pure {α : Type u} (a : α) : OptionT.lift (pure a : m α) = pure a := by
  simp only [OptionT.lift, OptionT.mk, bind_pure_comp, map_pure, pure, OptionT.pure]

@[simp]
theorem lift_bind {α β : Type u} (ma : m α) (f : α → m β) :
    OptionT.lift ma >>= (fun a => OptionT.lift (f a)) = OptionT.lift (ma >>= f) := by
  simp only [instMonad, OptionT.bind, OptionT.mk, OptionT.lift, bind_pure_comp, bind_map_left,
    map_bind]

instance : LawfulMonadLift m (OptionT m) where
  monadLift_pure := lift_pure
  monadLift_bind := lift_bind

end OptionT

namespace ExceptT

variable {ε : Type u} {m : Type u → Type v} [Monad m] [LawfulMonad m]

@[simp]
theorem lift_bind {α β : Type u} (ma : m α) (f : α → m β) :
    ExceptT.lift ma >>= (fun a => ExceptT.lift (f a)) = ExceptT.lift (ε := ε) (ma >>= f) := by
  simp only [instMonad, ExceptT.bind, mk, ExceptT.lift, bind_map_left, ExceptT.bindCont, map_bind]

instance : LawfulMonadLift m (ExceptT ε m) where
  monadLift_pure := lift_pure
  monadLift_bind := lift_bind

instance : LawfulMonadLift (Except ε) (ExceptT ε m) where
  monadLift_pure := by
    intro α a
    simp only [MonadLift.monadLift, mk, pure, Except.pure, ExceptT.pure]
  monadLift_bind := by
    intro α β ma f
    simp only [instMonad, ExceptT.bind, mk, MonadLift.monadLift, pure_bind, ExceptT.bindCont,
      Except.instMonad, Except.bind]
    rcases ma with _ | _ <;> simp

end ExceptT

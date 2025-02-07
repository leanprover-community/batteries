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
    [Monad m] [Monad n] [inst : MonadLift m n] : Prop where
  /-- Lifting preserves `pure` -/
  monadLift_pure {α : Type u} (a : α) : inst.monadLift (pure a) = pure a
  /-- Lifting preserves `bind` -/
  monadLift_bind {α β : Type u} (ma : m α) (f : α → m β) :
    inst.monadLift ma >>= (fun x => inst.monadLift (f x)) = inst.monadLift (ma >>= f)

/-- The `MonadLiftT` typeclass only contains the transitive lifting operation.
  `LawfulMonadLiftT` further asserts that lifting commutes with `pure` and `bind`:
```
monadLift (pure a) = pure a
monadLift ma >>= monadLift ∘ f = monadLift (ma >>= f)
```
-/
class LawfulMonadLiftT (m : Type u → Type v) (n : Type u → Type w) [Monad m] [Monad n]
    [inst : MonadLiftT m n] : Prop where
  /-- Lifting preserves `pure` -/
  monadLift_pure {α : Type u} (a : α) : inst.monadLift (pure a) = pure a
  /-- Lifting preserves `bind` -/
  monadLift_bind {α β : Type u} (ma : m α) (f : α → m β) :
    monadLift ma >>= (fun x => monadLift (f x)) = inst.monadLift (ma >>= f)

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

instance (m n o) [Monad m] [Monad n] [Monad o] [MonadLift n o] [MonadLiftT m n]
    [LawfulMonadLift n o] [LawfulMonadLiftT m n] : LawfulMonadLiftT m o where
  monadLift_pure := fun a => by
    simp only [monadLift, LawfulMonadLift.monadLift_pure, liftM_pure]
  monadLift_bind := fun ma f => by
    simp only [monadLift, LawfulMonadLift.monadLift_bind, liftM_bind]

instance (m) [Monad m] : LawfulMonadLiftT m m where
  monadLift_pure _ := rfl
  monadLift_bind _ _ := rfl

namespace StateT

variable {σ} [Monad m] [LawfulMonad m]

instance : LawfulMonadLift m (StateT σ m) where
  monadLift_pure _ := by
    simp only [MonadLift.monadLift]
    unfold StateT.lift StateT.instMonad StateT.bind StateT.pure
    simp only [bind_pure_comp, map_pure]
  monadLift_bind _ _ := by
    simp only [MonadLift.monadLift]
    unfold StateT.lift StateT.instMonad StateT.bind StateT.pure
    simp only [bind_pure_comp, Function.comp_apply, bind_map_left, map_bind]

end StateT

namespace ReaderT

variable {ρ} [Monad m]

instance : LawfulMonadLift m (ReaderT ρ m) where
  monadLift_pure _ := by
    funext x
    simp only [MonadLift.monadLift, pure, ReaderT.pure]
  monadLift_bind _ _ := by
    funext x
    simp only [bind, ReaderT.bind, MonadLift.monadLift, Function.comp_apply]

end ReaderT

namespace OptionT

variable [Monad m] [LawfulMonad m]

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

variable {ε} [Monad m] [LawfulMonad m]

@[simp]
theorem lift_bind {α β} (ma : m α) (f : α → m β) :
    ExceptT.lift ma >>= (fun a => ExceptT.lift (f a)) = ExceptT.lift (ε := ε) (ma >>= f) := by
  simp only [instMonad, ExceptT.bind, mk, ExceptT.lift, bind_map_left, ExceptT.bindCont, map_bind]

instance : LawfulMonadLift m (ExceptT ε m) where
  monadLift_pure := lift_pure
  monadLift_bind := lift_bind

instance : LawfulMonadLift (Except ε) (ExceptT ε m) where
  monadLift_pure _ := by
    simp only [MonadLift.monadLift, mk, pure, Except.pure, ExceptT.pure]
  monadLift_bind ma _ := by
    simp only [instMonad, ExceptT.bind, mk, MonadLift.monadLift, pure_bind, ExceptT.bindCont,
      Except.instMonad, Except.bind]
    rcases ma with _ | _ <;> simp

end ExceptT

namespace StateRefT'

instance {ω σ m} [Monad m] : LawfulMonadLift m (StateRefT' ω σ m) where
  monadLift_pure _ := by
    simp only [MonadLift.monadLift, pure]
    unfold StateRefT'.lift ReaderT.pure
    simp only
  monadLift_bind _ _ := by
    simp only [MonadLift.monadLift, bind]
    unfold StateRefT'.lift ReaderT.bind
    simp only

end StateRefT'

namespace StateCpsT

instance {σ m} [Monad m] [LawfulMonad m] : LawfulMonadLift m (StateCpsT σ m) where
  monadLift_pure _ := by
    simp only [MonadLift.monadLift, pure]
    unfold StateCpsT.lift
    simp only [pure_bind]
  monadLift_bind _ _ := by
    simp only [MonadLift.monadLift, bind]
    unfold StateCpsT.lift
    simp only [bind_assoc]

end StateCpsT

namespace ExceptCpsT

instance {ε m} [Monad m] [LawfulMonad m] : LawfulMonadLift m (ExceptCpsT ε m) where
  monadLift_pure _ := by
    simp [MonadLift.monadLift, pure]
    unfold ExceptCpsT.lift
    simp only [pure_bind]
  monadLift_bind _ _ := by
    simp only [MonadLift.monadLift, bind]
    unfold ExceptCpsT.lift
    simp only [bind_assoc]

end ExceptCpsT

instance {ε} : LawfulMonadLift BaseIO (EIO ε) where
  monadLift_pure _ := by
    simp only [MonadLift.monadLift, pure]
    unfold BaseIO.toEIO EStateM.pure
    simp only
  monadLift_bind ma f := by
    simp only [MonadLift.monadLift, bind]
    unfold BaseIO.toEIO EStateM.bind IO.RealWorld
    funext x
    simp only
    rcases ma x with a | a
    · simp only
    · contradiction

instance {ε σ} : LawfulMonadLift (ST σ) (EST ε σ) where
  monadLift_pure a := by
    simp [MonadLift.monadLift, pure]
    funext x
    rcases h : EStateM.pure a x with y | y
    · simp_all only [EStateM.pure, EStateM.Result.ok.injEq]
    · contradiction
  monadLift_bind ma f := by
    simp only [MonadLift.monadLift, bind]
    unfold EStateM.bind
    funext x
    simp
    rcases ma x with a | a
    · simp
    · contradiction

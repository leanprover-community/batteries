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
monadLift (ma >>= f) = monadLift ma >>= monadLift ∘ f
```
-/
class LawfulMonadLift (m : semiOutParam (Type u → Type v)) (n : Type u → Type w)
    [Monad m] [Monad n] [inst : MonadLift m n] : Prop where
  /-- Lifting preserves `pure` -/
  monadLift_pure {α : Type u} (a : α) : inst.monadLift (pure a) = pure a
  /-- Lifting preserves `bind` -/
  monadLift_bind {α β : Type u} (ma : m α) (f : α → m β) :
    inst.monadLift (ma >>= f) = inst.monadLift ma >>= (fun x => inst.monadLift (f x))

/-- The `MonadLiftT` typeclass only contains the transitive lifting operation.
  `LawfulMonadLiftT` further asserts that lifting commutes with `pure` and `bind`:
```
monadLift (pure a) = pure a
monadLift (ma >>= f) = monadLift ma >>= monadLift ∘ f
```
-/
class LawfulMonadLiftT (m : Type u → Type v) (n : Type u → Type w) [Monad m] [Monad n]
    [inst : MonadLiftT m n] : Prop where
  /-- Lifting preserves `pure` -/
  monadLift_pure {α : Type u} (a : α) : inst.monadLift (pure a) = pure a
  /-- Lifting preserves `bind` -/
  monadLift_bind {α β : Type u} (ma : m α) (f : α → m β) :
    inst.monadLift (ma >>= f) = monadLift ma >>= (fun x => monadLift (f x))

export LawfulMonadLiftT (monadLift_pure monadLift_bind)

variable {m : Type u → Type v} {n : Type u → Type w} {α β σ ρ ε ω}

section Lemmas

variable [Monad m] [Monad n] [MonadLiftT m n] [LawfulMonadLiftT m n]

theorem monadLift_map [LawfulMonad m] [LawfulMonad n] (f : α → β) (ma : m α) :
    monadLift (f <$> ma) = f <$> (monadLift ma : n α) := by
  rw [← bind_pure_comp, ← bind_pure_comp, monadLift_bind]
  simp only [bind_pure_comp, monadLift_pure]

theorem monadLift_seq [LawfulMonad m] [LawfulMonad n] (mf : m (α → β)) (ma : m α) :
    monadLift (mf <*> ma) = monadLift mf <*> (monadLift ma : n α) := by
  simp only [seq_eq_bind, monadLift_map, monadLift_bind]

theorem monadLift_seqLeft [LawfulMonad m] [LawfulMonad n] (x : m α) (y : m β) :
    monadLift (x <* y) = (monadLift x : n α) <* (monadLift y : n β) := by
  simp only [seqLeft_eq, monadLift_map, monadLift_seq]

theorem monadLift_seqRight [LawfulMonad m] [LawfulMonad n] (x : m α) (y : m β) :
    monadLift (x *> y) = (monadLift x : n α) *> (monadLift y : n β) := by
  simp only [seqRight_eq, monadLift_map, monadLift_seq]

/-! We duplicate the theorems for `monadLift` to `liftM` since `rw` matches on syntax only. -/

@[simp]
theorem liftM_pure (a : α) : liftM (pure a : m α) = pure (f := n) a :=
  monadLift_pure _

@[simp]
theorem liftM_bind (ma : m α) (f : α → m β) :
    liftM (n := n) (ma >>= f) = liftM ma >>= (fun a => liftM (f a)) :=
  monadLift_bind _ _

@[simp]
theorem liftM_map [LawfulMonad m] [LawfulMonad n] (f : α → β) (ma : m α) :
    liftM (f <$> ma) = f <$> (liftM ma : n α) :=
  monadLift_map _ _

@[simp]
theorem liftM_seq [LawfulMonad m] [LawfulMonad n] (mf : m (α → β)) (ma : m α) :
    liftM (mf <*> ma) = liftM mf <*> (liftM ma : n α) :=
  monadLift_seq _ _

@[simp]
theorem liftM_seqLeft [LawfulMonad m] [LawfulMonad n] (x : m α) (y : m β) :
    liftM (x <* y) = (liftM x : n α) <* (liftM y : n β) :=
  monadLift_seqLeft _ _

@[simp]
theorem liftM_seqRight [LawfulMonad m] [LawfulMonad n] (x : m α) (y : m β) :
    liftM (x *> y) = (liftM x : n α) *> (liftM y : n β) :=
  monadLift_seqRight _ _

instance (m n o) [Monad m] [Monad n] [Monad o] [MonadLift n o] [MonadLiftT m n]
    [LawfulMonadLift n o] [LawfulMonadLiftT m n] : LawfulMonadLiftT m o where
  monadLift_pure := fun a => by
    simp only [monadLift, LawfulMonadLift.monadLift_pure, liftM_pure]
  monadLift_bind := fun ma f => by
    simp only [monadLift, LawfulMonadLift.monadLift_bind, liftM_bind]

instance (m) [Monad m] : LawfulMonadLiftT m m where
  monadLift_pure _ := rfl
  monadLift_bind _ _ := rfl

end Lemmas

namespace StateT

variable [Monad m] [LawfulMonad m]

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

variable [Monad m]

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
theorem lift_pure (a : α) : OptionT.lift (pure a : m α) = pure a := by
  simp only [OptionT.lift, OptionT.mk, bind_pure_comp, map_pure, pure, OptionT.pure]

@[simp]
theorem lift_bind (ma : m α) (f : α → m β) :
    OptionT.lift (ma >>= f) = OptionT.lift ma >>= (fun a => OptionT.lift (f a)) := by
  simp only [instMonad, OptionT.bind, OptionT.mk, OptionT.lift, bind_pure_comp, bind_map_left,
    map_bind]

instance : LawfulMonadLift m (OptionT m) where
  monadLift_pure := lift_pure
  monadLift_bind := lift_bind

end OptionT

namespace ExceptT

variable [Monad m] [LawfulMonad m]

@[simp]
theorem lift_bind (ma : m α) (f : α → m β) :
    ExceptT.lift (ε := ε) (ma >>= f) = ExceptT.lift ma >>= (fun a => ExceptT.lift (f a)) := by
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

instance {m} [Monad m] : LawfulMonadLift m (StateRefT' ω σ m) where
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

instance [Monad m] [LawfulMonad m] : LawfulMonadLift m (StateCpsT σ m) where
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

instance [Monad m] [LawfulMonad m] : LawfulMonadLift m (ExceptCpsT ε m) where
  monadLift_pure _ := by
    simp only [MonadLift.monadLift, pure]
    unfold ExceptCpsT.lift
    simp only [pure_bind]
  monadLift_bind _ _ := by
    simp only [MonadLift.monadLift, bind]
    unfold ExceptCpsT.lift
    simp only [bind_assoc]

end ExceptCpsT

namespace Id

variable {m : Type u → Type v}

/-- The `pure` operation of a monad `m` can be seen as a lifting operation from `Id` to `m`. -/
instance [Pure m] : MonadLift Id m where
  monadLift := pure

/-- The lifting from `Id` to a lawful monad `m` induced by `pure` is lawful. -/
instance [Monad m] [LawfulMonad m] : LawfulMonadLift Id m where
  monadLift_pure := fun a => by simp [MonadLift.monadLift, pure]
  monadLift_bind := fun x f => by simp [MonadLift.monadLift, bind]

end Id

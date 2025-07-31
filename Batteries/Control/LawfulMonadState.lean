/-
Copyright (c) 2025 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
-/

/-!
# Laws for Monads with State

This file defines a typeclass for `MonadStateOf` with compatible `get` and `set` operations.

Note that we use `MonadStateOf` over `MonadState` as the first induces the second,
but we phrase things using `MonadStateOf.set` and `MonadState.get` as those are the
versions that are available at the top level namespace.
-/

/-- The namespaced `MonadStateOf.get` is equal to the `MonadState` provided `get`. -/
@[simp] theorem monadStateOf_get_eq_get [MonadStateOf σ m] :
    (MonadStateOf.get : m σ) = get := rfl

/-- The namespaced `MonadStateOf.modifyGet` is equal to the `MonadState` provided `modifyGet`. -/
@[simp] theorem monadStateOf_modifyGet_eq_modifyGet [MonadStateOf σ m]
    (f : σ → α × σ) : (MonadStateOf.modifyGet f : m α) = modifyGet f := rfl

@[simp] theorem liftM_get {m n}  [MonadStateOf σ m] [MonadLift m n] :
    (liftM (get (m := m)) : n _) = get := rfl

@[simp] theorem liftM_set {m n} [MonadStateOf σ m] [MonadLift m n]
    (s : σ) : (liftM (set (m := m) s) : n _) = set s := rfl

@[simp] theorem liftM_modify {m n} [MonadStateOf σ m] [MonadLift m n]
    (f : σ → σ) : (liftM (modify (m := m) f) : n _) = modify f := rfl

@[simp] theorem liftM_modifyGet {m n} [MonadStateOf σ m] [MonadLift m n]
    (f : σ → α × σ) : (liftM (modifyGet (m := m) f) : n _) = modifyGet f := rfl

@[simp] theorem liftM_getModify {m n} [MonadStateOf σ m] [MonadLift m n]
    (f : σ → σ) : (liftM (getModify (m := m) f) : n _) = getModify f := rfl

/-- Class for well behaved state monads, extending the base `MonadState` type.
Requires that `modifyGet` is equal to the same definition with only `get` and `set`,
that `get` is idempotent if the result isn't used, and that `get` after `set` returns
exactly the value that was previously `set`. -/
class LawfulMonadStateOf (σ : semiOutParam (Type _)) (m : Type _ → Type _)
    [Monad m] [MonadStateOf σ m] extends LawfulMonad m where
  /-- `modifyGet f` is equal to getting the state, modifying it, and returning a result. -/
  modifyGet_eq {α} (f : σ → α × σ) :
    modifyGet (m := m) f = do let z ← f <$> get; set z.2; return z.1
  /-- Discarding the result of `get` is the same as never getting the state. -/
  get_bind_const {α} (mx : m α) : (do let _ ← get; mx) = mx
  /-- Calling `get` twice is the same as just using the first retreived state value. -/
  get_bind_get_bind {α} (mx : σ → σ → m α) :
    (do let s ← get; let s' ← get; mx s s') = (do let s ← get; mx s s)
  /-- Setting the monad state to its current value has no effect. -/
  get_bind_set_bind {α} (mx : σ → PUnit → m α) :
    (do let s ← get; let u ← set s; mx s u) = (do let s ← get; mx s PUnit.unit)
  /-- Setting and then returning the monad state is the same as returning the set value. -/
  set_bind_get (s : σ) : (do set (m := m) s; get) = (do set s; return s)
  /-- Setting the monad twice is the same as just setting to the final state. -/
  set_bind_set (s s' : σ) : (do set (m := m) s; set s') = set s'

namespace LawfulMonadStateOf

variable {σ : Type _} {m : Type _ → Type _} [Monad m]
  [MonadStateOf σ m] [LawfulMonadStateOf σ m]

attribute [simp] get_bind_const get_bind_get_bind get_bind_set_bind set_bind_get set_bind_set

@[simp] theorem get_seqRight (mx : m α) : get *> mx = mx := by
  rw [seqRight_eq_bind, get_bind_const]

@[simp] theorem seqLeft_get (mx : m α) : mx <* get = mx := by
  simp only [seqLeft_eq_bind, get_bind_const, bind_pure]

@[simp] theorem get_map_const (x : α) :
    (fun _ => x) <$> get (m := m) = pure x := by
  rw [map_eq_pure_bind, get_bind_const]

theorem get_bind_get : (do let _ ← get (m := m); get) = get := get_bind_const get

@[simp] theorem get_bind_set :
    (do let s ← get (m := m); set s) = return PUnit.unit := by
  simpa only [bind_pure_comp, id_map', get_map_const] using
    get_bind_set_bind (σ := σ) (m := m) (fun _ _ => return PUnit.unit)

@[simp] theorem get_bind_map_set (f : σ → PUnit → α) :
    (do let s ← get (m := m); f s <$> set s) = (do return f (← get) PUnit.unit) := by
  simp [map_eq_pure_bind, -bind_pure_comp]

@[simp] theorem set_bind_get_bind (s : σ) (f : σ → m α) :
    (do set s; let s' ← get; f s') = (do set s; f s) := by
  rw [← bind_assoc, set_bind_get, bind_assoc, pure_bind]

@[simp] theorem set_bind_map_get (f : σ → α) (s : σ) :
    (do set (m := m) s; f <$> get) = (do set (m := m) s; pure (f s)) := by
  simp [map_eq_pure_bind, -bind_pure_comp]

@[simp] theorem set_bind_set_bind (s s' : σ) (mx : m α) :
    (do set s; set s'; mx) = (do set s'; mx) := by
  rw [← bind_assoc, set_bind_set]

@[simp] theorem set_bind_map_set (s s' : σ) (f : PUnit → α) :
    (do set (m := m) s; f <$> set s') = (do f <$> set s') := by
  simp [map_eq_pure_bind, ← bind_assoc, -bind_pure_comp]

section modify

theorem modifyGetThe_eq (f : σ → α × σ) :
    modifyGetThe σ (m := m) f = do let z ← f <$> get; set z.2; return z.1 := modifyGet_eq f

theorem modify_eq (f : σ → σ) :
    modify (m := m) f = (do set (f (← get))) := by simp [modify, modifyGet_eq]

theorem modifyThe_eq (f : σ → σ) :
    modifyThe σ (m := m) f = (do set (f (← get))) := modify_eq f

theorem getModify_eq (f : σ → σ) :
    getModify (m := m) f = do let s ← get; set (f s); return s := by
  rw [getModify, modifyGet_eq, bind_map_left]

/-- Version of `modifyGet_eq` that preserves an call to `modify`. -/
theorem modifyGet_eq' (f : σ → α × σ) :
    modifyGet (m := m) f = do let s ← get; modify (Prod.snd ∘ f); return (f s).fst := by
  simp [modify_eq, modifyGet_eq]

@[simp] theorem modify_id : modify (m := m) id = pure PUnit.unit := by
  simp [modify_eq]

@[simp] theorem getModify_id : getModify (m := m) id = get := by
  simp [getModify_eq]

@[simp] theorem set_bind_modify (s : σ) (f : σ → σ) :
    (do set (m := m) s; modify f) = set (f s) := by simp [modify_eq]

@[simp] theorem set_bind_modify_bind (s : σ) (f : σ → σ) (mx : PUnit → m α) :
    (do set s; let u ← modify f; mx u) = (do set (f s); mx PUnit.unit) := by
  simp [modify_eq, ← bind_assoc]

@[simp] theorem set_bind_modifyGet (s : σ) (f : σ → α × σ) :
    (do set (m := m) s; modifyGet f) = (do set (f s).2; return (f s).1) := by simp [modifyGet_eq]

@[simp] theorem set_bind_modifyGet_bind (s : σ) (f : σ → α × σ) (mx : α → m β) :
    (do set s; let x ← modifyGet f; mx x) = (do set (f s).2; mx (f s).1) := by simp [modifyGet_eq]

@[simp] theorem set_bind_getModify (s : σ) (f : σ → σ) :
    (do set (m := m) s; getModify f) = (do set (f s); return s) := by simp [getModify_eq]

@[simp] theorem set_bind_getModify_bind (s : σ) (f : σ → σ) (mx : σ → m α) :
    (do set s; let x ← getModify f; mx x) = (do set (f s); mx s) := by
  simp [getModify_eq, ← bind_assoc]

@[simp] theorem modify_bind_modify (f g : σ → σ) :
    (do modify (m := m) f; modify g) = modify (g ∘ f) := by simp [modify_eq]

@[simp] theorem modify_bind_modifyGet (f : σ → σ) (g : σ → α × σ) :
    (do modify (m := m) f; modifyGet g) = modifyGet (g ∘ f) := by
  simp [modify_eq, modifyGet_eq]

@[simp] theorem getModify_bind_modify (f : σ → σ) (g : σ → σ → σ) :
    (do let s ← getModify (m := m) f; modify (g s)) =
      (do let s ← get; modify (g s ∘ f)) := by
  simp [modify_eq, getModify_eq]

theorem modify_comm_of_comp_comm {f g : σ → σ} (h : f ∘ g = g ∘ f) :
    (do modify (m := m) f; modify g) = (do modify (m := m) g; modify f) := by
  simp [modify_bind_modify, h]

theorem modify_bind_get (f : σ → σ) :
    (do modify (m := m) f; get) = (do let s ← get; modify f; return (f s)) := by
  simp [modify_eq]

end modify

/-- `StateT` has lawful state operations if the underlying monad is lawful.
This is applied for `StateM` as well due to the reducibility of that definition. -/
instance {m σ} [Monad m] [LawfulMonad m] : LawfulMonadStateOf σ (StateT σ m) where
  modifyGet_eq f := StateT.ext fun s => by simp
  get_bind_const mx := StateT.ext fun s => by simp
  get_bind_get_bind mx := StateT.ext fun s => by simp
  get_bind_set_bind mx := StateT.ext fun s => by simp
  set_bind_get s := StateT.ext fun s => by simp
  set_bind_set s s' := StateT.ext fun s => by simp

/-- The continuation passing state monad variant `StateCpsT` always has lawful state instance. -/
instance {σ m} : LawfulMonadStateOf σ (StateCpsT σ m) where
  modifyGet_eq _ := rfl
  get_bind_const _ := rfl
  get_bind_get_bind _ := rfl
  get_bind_set_bind _ := rfl
  set_bind_get _ := rfl
  set_bind_set _ _ := rfl

/-- The `EStateM` monad always has a lawful state instance. -/
instance {σ ε} : LawfulMonadStateOf σ (EStateM ε σ) where
  modifyGet_eq _ := rfl
  get_bind_const _ := rfl
  get_bind_get_bind _ := rfl
  get_bind_set_bind _ := rfl
  set_bind_get _ := rfl
  set_bind_set _ _ := rfl

/-- If the underlying monad `m` has a lawful state instance, then the induced state instance on
`ReaderT ρ m` will also be lawful. -/
instance {m σ ρ} [Monad m] [LawfulMonad m] [MonadStateOf σ m] [LawfulMonadStateOf σ m] :
    LawfulMonadStateOf σ (ReaderT ρ m) where
  modifyGet_eq f := ReaderT.ext fun ctx => by
    simp [← liftM_modifyGet, LawfulMonadStateOf.modifyGet_eq, ← liftM_get]
  get_bind_const mx := ReaderT.ext fun ctx => by
    simp [← liftM_get]
  get_bind_get_bind mx := ReaderT.ext fun ctx => by
    simp [← liftM_get]
  get_bind_set_bind mx := ReaderT.ext fun ctx => by
    simp [← liftM_get, ← liftM_set]
  set_bind_get s := ReaderT.ext fun ctx => by
    simp [← liftM_get, ← liftM_set]
  set_bind_set s s' := ReaderT.ext fun ctx => by
    simp [← liftM_set]

instance {m ω σ} [Monad m] [LawfulMonad m] [MonadStateOf σ m] [LawfulMonadStateOf σ m] :
    LawfulMonadStateOf σ (StateRefT' ω σ m) :=
  inferInstanceAs (LawfulMonadStateOf σ (ReaderT _ _))

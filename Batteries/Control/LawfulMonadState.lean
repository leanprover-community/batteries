/-
Copyright (c) 2025 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
-/

/-!
# Laws for Monads with State

## Tags

monad, state
-/

/-- The namespaced `MonadStateOf.get` is equal to the `MonadState` provided `get`. -/
@[simp] theorem monadStateOf_get_eq_get [MonadStateOf σ m] :
    (MonadStateOf.get : m σ) = get := rfl

@[simp] theorem monadStateOf_modifyGet_eq_modifyGet [MonadStateOf σ m]
    (f : σ → α × σ) : (MonadStateOf.modifyGet f : m α) = modifyGet f := rfl

/-- Class for well behaved state monads, extending the base `MonadState` type.
Requires that `modifyGet` is equal to the same definition with only `get` and `set`,
that `get` is idempotent if the result isn't used, and that `get` after `set` returns
exactly the value that was previously `set`. -/
class LawfulMonadStateOf (σ : Type _) (m : Type _ → Type _) [Monad m] [MonadStateOf σ m] where
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

variable {σ : Type _} {m : Type _ → Type _} [Monad m] [MonadStateOf σ m] [LawfulMonadStateOf σ m]

namespace LawfulMonadStateOf

attribute [simp] get_bind_const get_bind_get_bind get_bind_set_bind set_bind_get set_bind_set

@[simp] theorem get_seqRight [LawfulMonad m] (mx : m α) : get *> mx = mx := by
  rw [seqRight_eq_bind, get_bind_const]

@[simp] theorem seqLeft_get [LawfulMonad m] (mx : m α) : mx <* get = mx := by
  simp only [seqLeft_eq_bind, get_bind_const, bind_pure]

@[simp] theorem get_map_const [LawfulMonad m] (x : α) :
    (fun _ => x) <$> get (m := m) = pure x := by
  rw [map_eq_pure_bind, get_bind_const]

@[simp] theorem get_bind_set [LawfulMonad m] :
    (do let s ← get (m := m); set s) = return PUnit.unit := by
  simpa only [bind_pure_comp, id_map', get_map_const] using
    get_bind_set_bind (σ := σ) (m := m) (fun _ _ => return PUnit.unit)

@[simp] theorem get_bind_map_set [LawfulMonad m] (f : σ → PUnit → α) :
    (do let s ← get (m := m); f s <$> set s) = (do return f (← get) PUnit.unit) := by
  simp [map_eq_pure_bind, bind_assoc, -bind_pure_comp]

@[simp] theorem set_bind_get_bind [LawfulMonad m] (s : σ) (f : σ → m α) :
    (do set s; let s' ← get; f s') = (do set s; f s) := by
  rw [← bind_assoc, set_bind_get, bind_assoc, pure_bind]

@[simp] theorem set_bind_map_get [LawfulMonad m] (f : σ → α) (s : σ) :
    (do set (m := m) s; f <$> get) = (do set (m := m) s; pure (f s)) := by
  simp [map_eq_pure_bind, -bind_pure_comp]

@[simp] theorem set_bind_set_bind [LawfulMonad m] (s s' : σ) (mx : m α) :
    (do set s; set s'; mx) = (do set s'; mx) := by
  rw [← bind_assoc, set_bind_set]

@[simp] theorem set_bind_map_set [LawfulMonad m] (s s' : σ) (f : PUnit → α) :
    (do set (m := m) s; f <$> set s') = (do f <$> set s') := by
  simp [map_eq_pure_bind, ← bind_assoc, -bind_pure_comp]

section modify

theorem modifyGetThe_eq (f : σ → α × σ) :
    modifyGetThe σ (m := m) f = do let z ← f <$> get; set z.2; return z.1 := modifyGet_eq f

theorem modify_eq [LawfulMonad m] (f : σ → σ) :
    modify (m := m) f = (do set (f (← get))) := by simp [modify, modifyGet_eq]

theorem modifyThe_eq [LawfulMonad m] (f : σ → σ) :
    modifyThe σ (m := m) f = (do set (f (← get))) := modify_eq f

theorem getModify_eq [LawfulMonad m] (f : σ → σ) :
    getModify (m := m) f = do let s ← get; set (f s); return s := by
  rw [getModify, modifyGet_eq, bind_map_left]

theorem modifyGet_eq' [LawfulMonad m] (f : σ → α × σ) :
    modifyGet (m := m) f = do let s ← get; modify (Prod.snd ∘ f); return (f s).fst := by
  simp [modify_eq, modifyGet_eq]

@[simp] theorem modify_id [LawfulMonad m] : modify (m := m) id = pure PUnit.unit := by
  simp [modify_eq]

@[simp] theorem getModify_id [LawfulMonad m] : getModify (m := m) id = get := by
  simp [getModify_eq]

@[simp] theorem modify_modify [LawfulMonad m] (f g : σ → σ) :
    (do modify (m := m) f; modify g) = modify (g ∘ f) := by
  simp [modify_eq]

@[simp] theorem modify_modifyGet [LawfulMonad m] (f : σ → σ) (g : σ → α × σ) :
    (do modify (m := m) f; modifyGet g) = modifyGet (g ∘ f) := by
  simp [modify_eq, modifyGet_eq]

end modify

end LawfulMonadStateOf

namespace StateT

instance [LawfulMonad m] : LawfulMonadStateOf σ (StateT σ m) where
  modifyGet_eq f := StateT.ext fun s => by simp
  get_bind_const mx := StateT.ext fun s => by simp
  get_bind_get_bind mx := StateT.ext fun s => by simp
  get_bind_set_bind mx := StateT.ext fun s => by simp
  set_bind_get s := StateT.ext fun s => by simp
  set_bind_set s s' := StateT.ext fun s => by simp

end StateT

namespace StateCpsT

instance : LawfulMonadStateOf σ (StateCpsT σ m) where
  modifyGet_eq _ := rfl
  get_bind_const _ := rfl
  get_bind_get_bind _ := rfl
  get_bind_set_bind _ := rfl
  set_bind_get _ := rfl
  set_bind_set _ _ := rfl

end StateCpsT

namespace EStateM

instance {ε} : LawfulMonadStateOf σ (EStateM ε σ) where
  modifyGet_eq _ := rfl
  get_bind_const _ := rfl
  get_bind_get_bind _ := rfl
  get_bind_set_bind _ := rfl
  set_bind_get _ := rfl
  set_bind_set _ _ := rfl

end EStateM

namespace OptionT

instance [Monad m] [MonadStateOf σ m] [LawfulMonadStateOf σ m] :
    LawfulMonadStateOf σ (OptionT m) where
  modifyGet_eq f := sorry
  get_bind_const := sorry
  get_bind_get_bind := sorry
  get_bind_set_bind := sorry
  set_bind_get := sorry
  set_bind_set := sorry

end OptionT

namespace WriterT

instance {ρ} [Monad m] [MonadStateOf σ m] [LawfulMonadStateOf σ m] :
    LawfulMonadStateOf σ (ReaderT ρ m) where
  modifyGet_eq f := sorry
  get_bind_const := sorry
  get_bind_get_bind := sorry
  get_bind_set_bind := sorry
  set_bind_get := sorry
  set_bind_set := sorry

end WriterT

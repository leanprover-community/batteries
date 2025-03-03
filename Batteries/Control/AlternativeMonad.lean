/-
Copyright (c) 2025 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import Batteries.Control.OptionT


/-!
# Laws for Monads with Failure

Definitions for monads that also have an `Alternative` instance while sharing the underlying
`Applicative` instance, and a class `LawfulAlternative` for types where the failure and monad
structures are compatible in a natural way. More specifically they satisfy:

* `failure >>= g = failure`
* `x <|> failure = x`
* `failure <|> y = y`
* `x <|> y <|> z = (x <|> y) <|> z`
* `f <$> (x <|> y) = (f <$> x <|> f <$> y)`

`Option`/`OptionT` are the most basic examples, but transformers like `StateT` also preserve
the lawfulness of this on the underlying monad.

The law `do _ ← x; failure = failure` is true for monads like `Option` and `List` that don't
have any "side effects" to execution, but not for something like `OptionT` on some monads,
so we don't include this condition.

We also define a class `LawfulAlternativeLift` similar to `LawfulMonadLift` that states that
a lifting between monads preserves `failure` and `orElse`.

## Tags

monad, alternative, failure
-/

universe u v w

/-- `AlternativeMonad m` means that `m` has both a `Monad` and `Alternative` instance,
which both share the same underlying `Applicative` instance.
The main example is `Option`, but many monad transformers also preserve or add this structure. -/
class AlternativeMonad (m : Type u → Type v) extends Alternative m, Monad m

/-- `LawfulAlternative m` means that the `failure` operation on `m` behaves naturally
with respect to the `bind` and `orElse` operators. -/
class LawfulAlternative (m : Type u → Type v) [AlternativeMonad m] extends LawfulMonad m where
  /-- `failure` ends a computation without running any remaining continuations. -/
  failure_bind {α β : Type u} (g : α → m β) : failure >>= g = failure
  /-- `failure` is a right identity for `orElse`. -/
  orElse_failure {α : Type u} (x : m α) : (x <|> failure) = x
  /-- `failure` is a left identity for `orElse`. -/
  failure_orElse {α : Type u} (y : m α) : (failure <|> y) = y
  /-- `orElse` is associative. -/
  orElse_assoc {α : Type u} (x y z : m α) : (x <|> y <|> z) = ((x <|> y) <|> z)
  /-- `map` commutes with `orElse`. The stronger statement with `bind` generally isn't true -/
  map_orElse {α β : Type u} (x y : m α) (f : α → β) : f <$> (x <|> y) = (f <$> x <|> f <$> y)

export LawfulAlternative (failure_bind orElse_failure failure_orElse orElse_assoc map_orElse)
attribute [simp] failure_bind orElse_failure failure_orElse map_orElse

section LawfulAlternative

variable {m : Type u → Type v} [AlternativeMonad m] [LawfulAlternative m]
    {n : Type → Type v} [AlternativeMonad n] [LawfulAlternative n]

@[simp] theorem map_failure {α β} (f : α → β) : f <$> (failure : m α) = failure := by
  rw [map_eq_pure_bind, failure_bind]

@[simp] theorem mapConst_failure {α β} (y : β) : Functor.mapConst y (failure : m α) = failure := by
  rw [LawfulFunctor.map_const, Function.comp_apply, map_failure]

@[simp] theorem mapConst_orElse {α β} (x x' : m α) (y : β) :
    Functor.mapConst y (x <|> x') = (Functor.mapConst y x <|> Functor.mapConst y x') := by
  simp only [map_const, Function.comp_apply, map_orElse]

@[simp] theorem failure_seq {α β} (x : m α) : (failure : m (α → β)) <*> x = failure := by
  rw [seq_eq_bind, failure_bind]

end LawfulAlternative

section LawfulAlternativeLift

/-- Type-class for monad lifts that preserve the `Alternative` operations. -/
class LawfulAlternativeLift (m : semiOutParam (Type u → Type v)) (n : Type u → Type w)
    [Alternative m] [Alternative n] [MonadLift m n] where
  /-- Lifting preserves `failure`. -/
  monadLift_failure {α} : monadLift (failure : m α) = (failure : n α)
  /-- Lifting preserves `orElse`. -/
  monadLift_orElse {α} (x y : m α) : monadLift (x <|> y) = (monadLift x <|> monadLift y : n α)

export LawfulAlternativeLift (monadLift_failure monadLift_orElse)
attribute [simp] monadLift_failure monadLift_orElse

variable {m : Type u → Type v} {n : Type u → Type w} [AlternativeMonad m] [AlternativeMonad n]
  [MonadLift m n] [LawfulAlternativeLift m n]

end LawfulAlternativeLift

namespace Option

instance : AlternativeMonad Option.{u} where

instance : LawfulAlternative Option.{u} where
  failure_bind _ := rfl
  orElse_failure := Option.orElse_none
  failure_orElse := Option.none_orElse
  orElse_assoc | some _, _, _ => rfl | none, _, _ => rfl
  map_orElse | some _ => by simp | none => by simp

end Option

namespace OptionT

variable {m : Type u → Type v} [Monad m]

instance : AlternativeMonad (OptionT m) where

instance [LawfulMonad m] : LawfulAlternative (OptionT m) where
  failure_bind _ := pure_bind _ _
  orElse_failure x := (bind_congr (fun | some _ => rfl | none => rfl)).trans (bind_pure x)
  failure_orElse _ := pure_bind _ _
  orElse_assoc _ _ _ := by
    simp only [OptionT.ext_iff, run_orElse, bind_assoc]
    refine bind_congr fun | some _ => by simp | none => rfl
  map_orElse x y f := by
    simp only [OptionT.ext_iff, run_map, run_orElse, map_bind, bind_map_left]
    refine bind_congr fun | some _ => by simp | none => rfl

end OptionT

namespace StateT

variable {m : Type u → Type v} [AlternativeMonad m] {σ : Type u}

instance : AlternativeMonad (StateT σ m) where

instance [LawfulAlternative m] : LawfulAlternative (StateT σ m) where
  failure_bind _ := StateT.ext fun _ => failure_bind _
  orElse_failure _ := StateT.ext fun _ => orElse_failure _
  failure_orElse _ := StateT.ext fun _ => failure_orElse _
  orElse_assoc _ _ _ := StateT.ext fun _ => orElse_assoc _ _ _
  map_orElse _ _ _ := StateT.ext fun _ => by simp only [run_map, run_orElse, map_orElse]

instance [LawfulAlternative m] : LawfulAlternativeLift m (StateT σ m) where
  monadLift_failure {α} := StateT.ext fun s => by simp
  monadLift_orElse {α} x y := StateT.ext fun s => by simp

end StateT

namespace ReaderT

variable {m : Type u → Type v} [AlternativeMonad m] {ρ : Type u}

instance : AlternativeMonad (ReaderT ρ m) where

instance [LawfulAlternative m] : LawfulAlternative (ReaderT ρ m) where
  failure_bind _ := ReaderT.ext fun _ => failure_bind _
  orElse_failure _ := ReaderT.ext fun _ => orElse_failure _
  failure_orElse _ := ReaderT.ext fun _ => failure_orElse _
  orElse_assoc _ _ _ := ReaderT.ext fun _ => orElse_assoc _ _ _
  map_orElse _ _ _ := ReaderT.ext fun _ => by simp only [run_map, run_orElse, map_orElse]

instance : LawfulAlternativeLift m (ReaderT ρ m) where
  monadLift_failure {α} := ReaderT.ext fun s => by simp
  monadLift_orElse {α} x y := ReaderT.ext fun s => by simp

end ReaderT

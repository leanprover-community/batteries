/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich
-/

import Batteries.Control.Lemmas

/-!
# Lemmas About Option Monad Transformer

This file contains lemmas about the behavior of `OptionT` and `OptionT.run`.
-/

universe u v

namespace OptionT

variable {α β : Type u} {m : Type u → Type v} (x : OptionT m α)

@[ext] theorem ext {x x' : OptionT m α} (h : x.run = x'.run) : x = x' := h

@[simp] theorem run_mk (x : m (Option α)) : OptionT.run (OptionT.mk x) = x := rfl

section Monad

variable [Monad m]

@[simp] theorem run_pure (a) : (pure a : OptionT m α).run = pure (some a) := rfl

@[simp]
theorem run_bind (f : α → OptionT m β) :
    (x >>= f).run = x.run >>= fun
                              | some a => OptionT.run (f a)
                              | none   => pure none := rfl

@[simp]
theorem run_map (f : α → β) [LawfulMonad m] : (f <$> x).run = Option.map f <$> x.run := by
  rw [← bind_pure_comp _ x.run]
  change x.run >>= (fun
                     | some a => OptionT.run (pure (f a))
                     | none   => pure none) = _
  apply bind_congr
  intro a; cases a <;> simp [Option.map, Option.bind]

@[simp] theorem run_monadLift {n} [MonadLiftT n m] (x : n α) :
    (monadLift x : OptionT m α).run = (monadLift x : m α) >>= fun a => pure (some a) := rfl

protected theorem mapConst_eq_map_const (y : β) (x : OptionT m α) :
    Functor.mapConst y x = Function.const α y <$> x := rfl

@[simp] theorem run_mapConst [LawfulMonad m] (x : OptionT m α) (y : β) :
    (Functor.mapConst y x).run = Option.map (Function.const α y) <$> x.run := by
  rw [OptionT.mapConst_eq_map_const, run_map]

instance (m : Type u → Type v) [Monad m] [LawfulMonad m] : LawfulMonad (OptionT m) :=
  LawfulMonad.mk'
    (id_map := by
      intros; apply OptionT.ext; simp only [OptionT.run_map]
      rw [map_congr, id_map]
      intro a; cases a <;> rfl)
    (bind_assoc := by
      intros; apply OptionT.ext; simp only [OptionT.run_bind, bind_assoc]
      rw [bind_congr]
      intro a; cases a <;> simp)
    (pure_bind := by intros; apply OptionT.ext; simp)

@[simp] theorem run_failure : (failure : OptionT m α).run = pure none := rfl

@[simp] theorem run_orElse (x : OptionT m α) (y : OptionT m α) :
    (x <|> y).run = Option.elimM x.run y.run (pure ∘ some) :=
  bind_congr fun | some _ => rfl | none => rfl

@[simp] theorem run_seq [LawfulMonad m] (f : OptionT m (α → β)) (x : OptionT m α) :
    (f <*> x).run = Option.elimM f.run (pure none) (fun f => Option.map f <$> x.run) := by
  simp only [seq_eq_bind, run_bind, run_map]
  refine bind_congr (fun | some _ => rfl | none => rfl)

@[simp] theorem run_seqLeft [LawfulMonad m] (x : OptionT m α) (y : OptionT m β) :
    (x <* y).run = Option.elimM x.run (pure none)
      (fun x => Option.map (Function.const β x) <$> y.run) := by
  simp [seqLeft_eq, seq_eq_bind, Option.elimM]
  refine bind_congr (fun | some _ => rfl | none => rfl)

@[simp] theorem run_seqRight [LawfulMonad m] (x : OptionT m α) (y : OptionT m β) :
    (x *> y).run = Option.elimM x.run (pure none) (Function.const α y.run) := by
  simp [seqRight_eq, Option.elimM, Option.elim]
  refine bind_congr (fun | some _ => by simp [Option.elim] | none => by simp [Option.elim])

end Monad

@[simp] theorem run_monadMap {n} [MonadFunctorT n m] (f : ∀ {α}, n α → n α) :
    (monadMap (@f) x : OptionT m α).run = monadMap (@f) x.run := rfl

end OptionT

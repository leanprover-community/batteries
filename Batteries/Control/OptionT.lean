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

namespace Option

@[simp] theorem elimM_pure [Monad m] [LawfulMonad m] (x : Option α) (y : m β)
    (z : α → m β) : Option.elimM (pure x) y z = Option.elim x y z := by
  simp [Option.elimM, Option.elim]

@[simp] theorem elimM_bind [Monad m] [LawfulMonad m] (x : m α) (f : α → m (Option β))
    (y : m γ) (z : β → m γ) : Option.elimM (x >>= f) y z = (do Option.elimM (f (← x)) y z) := by
  simp [Option.elimM]

@[simp] theorem elimM_map [Monad m] [LawfulMonad m] (x : m α) (f : α → Option β)
    (y : m γ) (z : β → m γ) : Option.elimM (f <$> x) y z = (do Option.elim (f (← x)) y z) := by
  simp [Option.elimM]

end Option

namespace OptionT

@[ext] theorem ext {x x' : OptionT m α} (h : x.run = x'.run) : x = x' := h

@[simp] theorem run_mk {m : Type _ → Type _} (x : m (Option α)) :
    OptionT.run (OptionT.mk x) = x := rfl

@[simp] theorem run_pure (a) [Monad m] : (pure a : OptionT m α).run = pure (some a) := rfl

@[simp] theorem run_bind (f : α → OptionT m β) [Monad m] :
    (x >>= f).run = Option.elimM x.run (pure none) (run ∘ f) := by
  change x.run >>= _ = _
  simp [Option.elimM]
  exact bind_congr fun |some _ => rfl | none => rfl

@[simp] theorem run_map (x : OptionT m α) (f : α → β) [Monad m] [LawfulMonad m] :
    (f <$> x).run = Option.map f <$> x.run := by
  rw [← bind_pure_comp _ x.run]
  change x.run >>= _ = _
  exact bind_congr fun |some _ => rfl | none => rfl

@[simp] theorem run_monadLift [Monad m] [LawfulMonad m] [MonadLiftT n m] (x : n α) :
    (monadLift x : OptionT m α).run = some <$> (monadLift x : m α) := (map_eq_pure_bind _ _).symm

@[simp] theorem run_mapConst [Monad m] [LawfulMonad m] (x : OptionT m α) (y : β) :
    (Functor.mapConst y x).run = Option.map (Function.const α y) <$> x.run := run_map _ _

instance (m) [Monad m] [LawfulMonad m] : LawfulMonad (OptionT m) :=
  LawfulMonad.mk'
    (id_map := by
      intros; apply OptionT.ext; simp only [OptionT.run_map]
      rw [map_congr, id_map]
      intro a; cases a <;> rfl)
    (bind_assoc := by
      refine fun _ _ _ => OptionT.ext ?_
      simp only [run_bind, Option.elimM, bind_assoc]
      refine bind_congr fun | some x => by simp [Option.elimM] | none => by simp [Option.elimM])
    (pure_bind := by intros; apply OptionT.ext; simp)

@[simp] theorem run_failure [Monad m] : (failure : OptionT m α).run = pure none := rfl

@[simp] theorem run_orElse [Monad m] (x : OptionT m α) (y : OptionT m α) :
    (x <|> y).run = Option.elimM x.run y.run (pure ∘ some) :=
  bind_congr fun | some _ => rfl | none => rfl

@[simp] theorem run_seq [Monad m] [LawfulMonad m] (f : OptionT m (α → β)) (x : OptionT m α) :
    (f <*> x).run = Option.elimM f.run (pure none) (fun f => Option.map f <$> x.run) := by
  simp only [seq_eq_bind, run_bind, run_map, Function.comp_def]

@[simp] theorem run_seqLeft [Monad m] [LawfulMonad m] (x : OptionT m α) (y : OptionT m β) :
    (x <* y).run = Option.elimM x.run (pure none)
      (fun x => Option.map (Function.const β x) <$> y.run) := by
  simp [seqLeft_eq, seq_eq_bind, Option.elimM, Function.comp_def]

@[simp] theorem run_seqRight [Monad m] [LawfulMonad m] (x : OptionT m α) (y : OptionT m β) :
    (x *> y).run = Option.elimM x.run (pure none) (Function.const α y.run) := by
  simp only [seqRight_eq, run_seq, run_map, Option.elimM_map]
  refine bind_congr (fun | some _ => by simp [Option.elim] | none => by simp [Option.elim])

@[simp] theorem run_monadMap {n} [MonadFunctorT n m] (f : ∀ {α}, n α → n α) :
    (monadMap (@f) x : OptionT m α).run = monadMap (@f) x.run := rfl

end OptionT

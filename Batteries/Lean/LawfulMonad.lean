/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Lean.Elab.Command
import all Init.System.ST

@[expose] public section

/-!
# Construct `LawfulMonad` instances for the Lean monad stack.
-/

open Lean Elab Term Tactic Command

instance : LawfulMonad (ST σ) := .mk' _
  (id_map := fun x => rfl)
  (pure_bind := fun x f => rfl)
  (bind_assoc := fun f g x => rfl)

instance  : LawfulMonad (EST ε σ) := .mk' _
  (id_map := fun x => funext fun v => by dsimp [Functor.map, EST.bind]; cases x v <;> rfl)
  (pure_bind := fun x f => rfl)
  (bind_assoc := fun f g x => funext fun v => by dsimp [Bind.bind, EST.bind]; cases f v <;> rfl)

instance : LawfulMonad (EIO ε) := inferInstanceAs <| LawfulMonad (EST _ _)
instance : LawfulMonad BaseIO := inferInstanceAs <| LawfulMonad (ST _)
instance : LawfulMonad IO := inferInstanceAs <| LawfulMonad (EIO _)

instance : LawfulMonad CoreM :=
  inferInstanceAs <| LawfulMonad (ReaderT _ <| StateRefT' _ _ (EIO Exception))
instance : LawfulMonad MetaM :=
  inferInstanceAs <| LawfulMonad (ReaderT _ <| StateRefT' _ _ CoreM)
instance : LawfulMonad TermElabM :=
  inferInstanceAs <| LawfulMonad (ReaderT _ <| StateRefT' _ _ MetaM)
instance : LawfulMonad TacticM :=
  inferInstanceAs <| LawfulMonad (ReaderT _ $ StateRefT' _ _ $ TermElabM)
instance : LawfulMonad CommandElabM :=
  inferInstanceAs <| LawfulMonad (ReaderT _ $ StateRefT' _ _ $ EIO _)

/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Batteries.Classes.SatisfiesM
import Batteries.Lean.LawfulMonad
import Lean.Elab.Command

/-!
# Construct `MonadSatisfying` instances for the Lean monad stack.
-/

open Lean Elab Term Tactic Command

instance : MonadSatisfying (EIO ε) := inferInstanceAs <| MonadSatisfying (EStateM _ _)
instance : MonadSatisfying BaseIO := inferInstanceAs <| MonadSatisfying (EIO _)
instance : MonadSatisfying IO := inferInstanceAs <| MonadSatisfying (EIO _)

instance : MonadSatisfying (EST ε σ) := inferInstanceAs <| MonadSatisfying (EStateM _ _)

instance : MonadSatisfying CoreM :=
  inferInstanceAs <| MonadSatisfying (ReaderT _ <| StateRefT' _ _ (EIO _))

instance : MonadSatisfying MetaM :=
  inferInstanceAs <| MonadSatisfying (ReaderT _ <| StateRefT' _ _ CoreM)

instance : MonadSatisfying TermElabM :=
  inferInstanceAs <| MonadSatisfying (ReaderT _ <| StateRefT' _ _ MetaM)

instance : MonadSatisfying TacticM :=
  inferInstanceAs <| MonadSatisfying (ReaderT _ $ StateRefT' _ _ TermElabM)

instance : MonadSatisfying CommandElabM :=
  inferInstanceAs <| MonadSatisfying (ReaderT _ $ StateRefT' _ _ (EIO _))

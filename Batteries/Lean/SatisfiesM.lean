/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Batteries.Classes.SatisfiesM
import Lean.Elab.Command

/-!
# Construct `Satisfying` instances for the Lean monad stack.
-/

open Lean Elab Term Tactic Command

instance : Satisfying CoreM :=
  inferInstanceAs <| Satisfying (ReaderT _ <| StateRefT' _ _ (EIO _))

instance : Satisfying MetaM :=
  inferInstanceAs <| Satisfying (ReaderT _ <| StateRefT' _ _ CoreM)

instance : Satisfying TermElabM :=
  inferInstanceAs <| Satisfying (ReaderT _ <| StateRefT' _ _ MetaM)

instance : Satisfying TacticM :=
  inferInstanceAs <| Satisfying (ReaderT _ $ StateRefT' _ _ TermElabM)

instance : Satisfying CommandElabM :=
  inferInstanceAs <| Satisfying (ReaderT _ $ StateRefT' _ _ (EIO _))

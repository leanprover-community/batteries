/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Batteries.Classes.SatisfiesM
public import Batteries.Lean.LawfulMonad
public import Lean.Elab.Command
import all Init.System.ST

@[expose] public section

/-!
# Construct `MonadSatisfying` instances for the Lean monad stack.
-/

open Lean Elab Term Tactic Command

-- Note: as of nightly-2025-10-23, after https://github.com/leanprover/lean4/pull/10625
-- these instances need to be re-implemented.

-- instance : MonadSatisfying (ST σ) where
--   satisfying {α p x} h := sorry
--   val_eq h := sorry

-- instance : MonadSatisfying (EST ε σ) where
--   satisfying h := sorry
--   val_eq h := sorry

-- instance : MonadSatisfying (EIO ε) := inferInstanceAs <| MonadSatisfying (EST _ _)
-- instance : MonadSatisfying BaseIO := inferInstanceAs <| MonadSatisfying (ST _)
-- instance : MonadSatisfying IO := inferInstanceAs <| MonadSatisfying (EIO _)

-- instance : MonadSatisfying CoreM :=
--   inferInstanceAs <| MonadSatisfying (ReaderT _ <| StateRefT' _ _ (EIO _))

-- instance : MonadSatisfying MetaM :=
--   inferInstanceAs <| MonadSatisfying (ReaderT _ <| StateRefT' _ _ CoreM)

-- instance : MonadSatisfying TermElabM :=
--   inferInstanceAs <| MonadSatisfying (ReaderT _ <| StateRefT' _ _ MetaM)

-- instance : MonadSatisfying TacticM :=
--   inferInstanceAs <| MonadSatisfying (ReaderT _ $ StateRefT' _ _ TermElabM)

-- instance : MonadSatisfying CommandElabM :=
--   inferInstanceAs <| MonadSatisfying (ReaderT _ $ StateRefT' _ _ (EIO _))

/-
Copyright (c) 2023 James Gallicchio.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James Gallicchio
-/

instance [Monad m] : MonadLift (StateM σ) (StateT σ m) where
  monadLift s := pure ∘ s

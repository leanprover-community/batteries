/-
Copyright (c) 2021 Shing Tak Lam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shing Tak Lam, Daniel Selsam, Mario Carneiro
-/
import Lean.Modifiers

namespace Lean

/--
Options to control `getMatchingConstants` options below.
-/
structure EnvironmentSearchOptions where
  /-- Include declarations in imported environment. -/
  stage1       : Bool := true
  /-- Include private declarations. -/
  checkPrivate : Bool := false

/--
Find constants in current environment that match find options and predicate.
-/
def getMatchingConstants {m} [Monad m] [MonadEnv m]
    (p : ConstantInfo → m Bool)
    (opts : EnvironmentSearchOptions := {})
    : m (Array ConstantInfo) := do
  let matches_ ←
    if opts.stage1 then
      (← getEnv).constants.map₁.foldM (init := #[]) check
    else
      pure #[]
  (← getEnv).constants.map₂.foldlM (init := matches_) check
where
  /-- Check constant should be returned -/
  check matches_ name cinfo := do
    if opts.checkPrivate || !isPrivateName name then
      if ← p cinfo then
        pure $ matches_.push cinfo
      else
        pure matches_
    else
      pure matches_

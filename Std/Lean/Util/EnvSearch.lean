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
  imported : Bool := true
  /--
  Set to true to include internal declarations (names with "_" or ending with match_ or proof_)
  -/
  internals : Bool := false

/--
Returns true if any part of name starts with underscore or uses a num.

This can be used to hide internally generated names.
-/
def isInternalDetail : Name → Bool
  | .str p s     =>
    s.startsWith "_"
      || s.startsWith "match_"
      || s.startsWith "proof_"
      || p.isInternal
  | .num p _     => p.isInternal
  | _            => false

/--
Find constants in current environment that match find options and predicate.
-/
def getMatchingConstants {m} [Monad m] [MonadEnv m]
    (p : ConstantInfo → m Bool)
    (opts : EnvironmentSearchOptions := {})
    : m (Array ConstantInfo) := do
  let matches_ ←
    if opts.imported then
      (← getEnv).constants.map₁.foldM (init := #[]) check
    else
      pure #[]
  (← getEnv).constants.map₂.foldlM (init := matches_) check
where
  /-- Check constant should be returned -/
  check matches_ name cinfo := do
    let runFilter : Bool := opts.internals || !isInternalDetail name
    let include ← if runFilter then p cinfo else pure false
    if include then
      pure $ matches_.push cinfo
    else
      pure matches_

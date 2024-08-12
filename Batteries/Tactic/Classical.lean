/-
Copyright (c) 2021 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Lean.Elab.Tactic.Basic

/-! # `classical` tactic -/

namespace Batteries.Tactic
open Lean Meta Elab.Tactic

/--
`classical t` runs `t` in a scope where `Classical.propDecidable` is a low priority
local instance.
-/
def classical [Monad m] [MonadEnv m] [MonadFinally m] [MonadLiftT MetaM m] (t : m α) :
    m α := do
  modifyEnv Meta.instanceExtension.pushScope
  Meta.addInstance ``Classical.propDecidable .local 10
  try
    t
  finally
    modifyEnv Meta.instanceExtension.popScope

/-- `classical!` has been removed; use `classical` instead -/
-- Deprecated 2024-04-19
elab "classical!" : tactic => do
  throwError "`classical!` has been removed; use `classical` instead"

/--
`classical tacs` runs `tacs` in a scope where `Classical.propDecidable` is a low priority
local instance.

Note that (unlike lean 3) `classical` is a scoping tactic - it adds the instance only within the
scope of the tactic.
-/
-- FIXME: using ppDedent looks good in the common case, but produces the incorrect result when
-- the `classical` does not scope over the rest of the block.
elab "classical" tacs:ppDedent(tacticSeq) : tactic => do
  classical <| Elab.Tactic.evalTactic tacs

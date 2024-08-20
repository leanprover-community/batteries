/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Batteries.Lean.Meta.Basic
import Lean.Meta.Tactic.Clear

open Lean Lean.Meta

/--
Try to clear the given fvars from the local context. Returns the new goal and
the hypotheses that were cleared. Unlike `Lean.MVarId.tryClearMany`, this
function does not require the `hyps` to be given in the order in which they
appear in the local context.
-/
def Lean.MVarId.tryClearMany' (goal : MVarId) (hyps : Array FVarId) :
    MetaM (MVarId × Array FVarId) :=
  goal.withContext do
    let hyps ← sortFVarsByContextOrder hyps
    hyps.foldrM (init := (goal, Array.mkEmpty hyps.size))
      fun h (goal, cleared) => do
        let goal' ← goal.tryClear h
        let cleared := if goal == goal' then cleared else cleared.push h
        return (goal', cleared)

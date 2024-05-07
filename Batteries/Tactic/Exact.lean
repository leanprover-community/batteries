/-
Copyright (c) 2023 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Lean.Meta.Tactic.Util

/-! # `exact` tactic (`MetaM` version) -/

open Lean Meta

/--
`MetaM` version of `Lean.Elab.Tactic.evalExact`: add `mvarId := x` to the metavariable assignment.
This method wraps `Lean.MVarId.assign`, checking whether `mvarId` is already assigned, and whether
the expression has the right type. -/
def Lean.MVarId.assignIfDefeq (g : MVarId) (e : Expr) : MetaM Unit := do
  guard <| ← isDefEq (← g.getType) (← inferType e)
  g.checkNotAssigned `assignIfDefeq
  g.assign e

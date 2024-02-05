/-
Copyright (c) 2024 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joe Hendrix
-/
import Lean.Elab.Tactic.ElabTerm

/-
This file is the home for commands to tactics behave as expected.

It currently includes two tactixs:

#check_tactic t ~> res


only a #check_simp command that applies simp
IT
-/

namespace Std.Tactic

open Lean
open Elab.Tactic
open Meta

/--
Type used to lift an arbitrary value into a type parameter so it can
appear in a proof goal.

It is used by the #check_tactic command.
-/
private inductive CheckGoalType {α : Sort u} : (val : α) → Prop where
| intro : (val : α) → CheckGoalType val

/--
`check_tactic_goal t` verifies that the goal has is equal to
`CheckGoalType t` with reducible transparency.  It closes the goal if so
and otherwise reports an error.

It is used by #check_tactic.
-/
local syntax (name := check_tactic_goal) "check_tactic_goal " term : tactic


/--
Implementation of `check_tactic_goal`
-/
@[tactic check_tactic_goal] private def evalCheckTacticGoal : Tactic := fun stx =>
  match stx with
  | `(tactic| check_tactic_goal $exp) =>
    closeMainGoalUsing (checkUnassigned := false) fun goalType => do
      let u ← mkFreshLevelMVar
      let type ← mkFreshExprMVar (.some (.sort u))
      let val  ← mkFreshExprMVar (.some type)
      let extType := mkAppN (.const ``CheckGoalType [u]) #[type, val]
      if !(← isDefEq goalType extType) then
        throwErrorAt stx "Goal{indentExpr goalType}\nis expected to match {indentExpr extType}"
      let expTerm ← elabTermEnsuringType exp type
      if !(← Meta.withReducible <| isDefEq val expTerm) then
        throwErrorAt stx
          m!"Term reduces to{indentExpr val}\nbut is expected to reduce to {indentExpr expTerm}"
      return mkAppN (.const ``CheckGoalType.intro [u]) #[type, val]
  | _ => throwErrorAt stx "check_goal syntax error"

/--
`#check_tactic t ~> r by commands` runs the tactic sequence `commands`
on a goal with t in the type and sees if the resulting expression has
reduced it to `r`.
-/
macro "#check_tactic " t:term "~>" result:term "by" tac:tactic : command =>
  `(command|example : CheckGoalType $t := by $tac; check_tactic_goal $result)

/--
`#check_simp t ~> r` checks `try simp` reduces `t` to `r`.
-/
macro "#check_simp " t:term "~>" exp:term : command =>
  `(command|#check_tactic $t ~> $exp by try simp)

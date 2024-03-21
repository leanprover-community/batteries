/-
Copyright (c) 2024 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joe Hendrix
-/
import Lean.Elab.Tactic.ElabTerm
import Lean.Elab.Term

/-
This file is the home for commands to tactics behave as expected.

It currently includes two tactixs:

#check_tactic t ~> res


only a #check_simp command that applies simp
IT
-/

namespace Std.Tactic

open Lean Elab Tactic
open Meta

/--
Type used to lift an arbitrary value into a type parameter so it can
appear in a proof goal.

It is used by the #check_tactic command.
-/
private inductive CheckGoalType {α : Sort u} : (val : α) → Prop where
| intro : (val : α) → CheckGoalType val

private def matchCheckGoalType (stx : Syntax) (goalType : Expr) : MetaM (Expr × Expr × Level) := do
    let u ← mkFreshLevelMVar
    let type ← mkFreshExprMVar (some (.sort u))
    let val  ← mkFreshExprMVar (some type)
    let extType := mkAppN (.const ``CheckGoalType [u]) #[type, val]
    if !(← isDefEq goalType extType) then
      throwErrorAt stx "Goal{indentExpr goalType}\nis expected to match {indentExpr extType}"
    pure (val, type, u)

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
      let (val, type, u) ← matchCheckGoalType stx goalType
      let expTerm ← elabTermEnsuringType exp type
      if !(← Meta.withReducible <| isDefEq val expTerm) then
        throwErrorAt stx
          m!"Term reduces to{indentExpr val}\nbut is expected to reduce to {indentExpr expTerm}"
      return mkAppN (.const ``CheckGoalType.intro [u]) #[type, val]
  | _ => throwErrorAt stx "check_goal syntax error"

/--
`check_tactic_goal t` verifies that the goal has is equal to
`CheckGoalType t` with reducible transparency.  It closes the goal if so
and otherwise reports an error.

It is used by #check_tactic.
-/
local syntax (name := check_tactic_fails) "check_tactic_fails " tactic : tactic

@[tactic check_tactic_fails] private def evalCheckTacticFails : Tactic := fun stx => do
  let `(tactic| check_tactic_fails $tactic) := stx
      | throwUnsupportedSyntax
  closeMainGoalUsing (checkUnassigned := false) fun goalType => do
    let (val, type, u) ← matchCheckGoalType stx goalType
    Term.withoutErrToSorry <| withoutRecover do
      match (← try (some <$> evalTactic tactic) catch _ => pure none) with
      | none =>
        return mkAppN (.const ``CheckGoalType.intro [u]) #[type, val]
      | some () =>
        let gls ← getGoals
        let ppGoal (g : MVarId) := do
              let (val, _type, _u) ← matchCheckGoalType stx (← g.getType)
              pure m!"{indentExpr val}"
        let msg ←
          match gls with
            | [] => pure m!"{tactic} expected to fail on {val}, but closed goal."
            | [g] =>
               pure <| m!"{tactic} expected to fail on {val}, but returned: {←ppGoal g}"
            | gls =>
              let app m g := do pure <| m ++ (←ppGoal g)
              let init := m!"{tactic} expected to fail on {val}, but returned goals:"
              gls.foldlM (init := init) app
        throwErrorAt stx msg

/--
`#check_tactic t ~> r by commands` runs the tactic sequence `commands`
on a goal with t in the type and sees if the resulting expression has
reduced it to `r`.
-/
macro "#check_tactic " t:term "~>" result:term "by" tac:tactic : command =>
  `(command|example : CheckGoalType $t := by $tac; check_tactic_goal $result)

/--
`#check_simp t ~> r` checks `simp` reduces `t` to `r`.
-/
macro "#check_simp " t:term "~>" exp:term : command =>
  `(command|#check_tactic $t ~> $exp by simp)

example (x : Nat) : CheckGoalType ((x + z) = x) := by
  fail_if_success simp []
  exact (CheckGoalType.intro ((x + z) = x))

/--
`#check_simp t !~>` checks `simp` fails to reduce `t`.
-/
macro "#check_simp " t:term "!~>" : command =>
  `(command|example : CheckGoalType $t := by check_tactic_fails simp)

/-
Copyright (c) 2022 Arthur Paulino. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Paulino, Mario Carneiro
-/
module

public meta import Lean.Elab.Tactic.Basic

public meta section

/-!
# The `on_goal`, `pick_goal`, and `swap` tactics.

`pick_goal n` moves the `n`-th goal to the front. If `n` is negative this is counted from the back.

`on_goal n => tacSeq` focuses on the `n`-th goal and runs a tactic block `tacSeq`.
If `tacSeq` does not close the goal any resulting subgoals are inserted back into the list of goals.
If `n` is negative this is counted from the back.

`swap` is a shortcut for `pick_goal 2`, which interchanges the 1st and 2nd goals.
-/

namespace Batteries.Tactic

open Lean Elab.Tactic

/-- A number referring to a goal in the tactic state. `n` refers to the `n`-th goal from the front,
and `-n` refers to the `n`-th goal from the bottom. -/
syntax goalNum := "-"? num

/-- Turn the given `goalNum` syntax into a (zero-based) index in the current `getGoals` list. -/
def elabGoalNum (goalNum : Syntax) : TacticM Nat := withRef goalNum do
  let nGoals := (← getGoals).length
  let some nth := goalNum[1].isNatLit? | Elab.throwUnsupportedSyntax
  if nth = 0 then throwError "goals are 1-indexed"
  if nth > nGoals then throwError "goal index `{nth}` is out of bounds"
  return if goalNum[0].isNone then nth - 1 else nGoals - nth

/--
`pick_goal n` will move the `n`-th goal to the front.

`pick_goal -n` will move the `n`-th goal (counting from the bottom) to the front.

See also `rotate_left`/`rotate_right`, which move goals from the front to the back and vice-versa.
-/
elab "pick_goal " n:goalNum : tactic => do
  let n ← elabGoalNum n
  let (gl, g :: gr) := (← getGoals).splitAt n | throwNoGoalsToBeSolved
  setGoals $ g :: (gl ++ gr)

/-- `swap` is a shortcut for `pick_goal 2`, which interchanges the 1st and 2nd goals. -/
macro "swap" : tactic => `(tactic| pick_goal 2)

/--
`on_goal n => tacSeq` creates a block scope for the `n`-th goal and tries the sequence
of tactics `tacSeq` on it.

`on_goal -n => tacSeq` does the same, but the `n`-th goal is chosen by counting from the
bottom.

`on_goal n₁ ... nᵢ => tacSeq` runs `tacSeq` on each of the goals `n₁ ... nᵢ` separately.

The goal is not required to be solved and any resulting subgoals are inserted back into the
list of goals, replacing the chosen goal.
-/
elab "on_goal " ns:goalNum+ " => " seq:tacticSeq : tactic => do
  let ns ← ns.mapM elabGoalNum
  let mut newGoals := #[]
  for goal in ← getGoals, i in 0...* do
    if ns.contains i then
      setGoals [goal]
      evalTactic seq
      newGoals := newGoals ++ (← getUnsolvedGoals)
    else
      newGoals := newGoals.push goal
  setGoals newGoals.toList

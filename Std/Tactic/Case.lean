/-
Copyright (c) 2023 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
import Lean.Elab.Tactic

/-!
# Extensions to the `case` tactic

Adds a variant of `case` that looks for a goal with a particular type, rather than a goal
with a particular tag.
-/

namespace Std.Tactic
open Lean Meta Elab Tactic

/-- Clause for a `case : ...` tactic. -/
syntax casePattArg := term (" with" (ppSpace colGt binderIdent)+)?

/--
* `case : t => tac` finds the first goal that unifies with `t` and then solves it
  using `tac` or else fails. Like `show`, it changes the type of the goal to `t`.

* `case : t with n₁ ... nₘ => tac` additionally names the `m` most recent hypotheses with
  inaccessible names to the given names.

* `case : t := e` is short for `case : t => exact e`.

* `case : t₁ | t₂ | ... => tac` is equivalent to `(case : t₁ => tac); (case : t₂ => tac); ...`.
  This supports `with` clauses.

* `case : t` will make the matched goal be the first goal. `case : t₁ | t₂ | ...` makes the
  matched goals be the first goals in the given order.
-/
syntax (name := casePatt) "case" " : " sepBy1(casePattArg, " | ") (" => " tacticSeq)? : tactic

@[inherit_doc casePatt]
macro "case" " : " cs:sepBy1(casePattArg, " | ") " := " colGt t:term : tactic =>
  `(tactic| (case : $[$cs]|* ; exact $t))

/-- Find the first goal whose type unifies with `patt` and make it be the first goal.
The `renameI` array consists of names to use to rename inaccessibles.
The `patt` term is elaborated in the context where the inaccessibles have been renamed. -/
def showGoalOfPatt (patt : Term) (renameI : TSyntaxArray `Lean.binderIdent) :
    TacticM (MVarId × List MVarId) :=
  Term.withoutErrToSorry <| withoutRecover do
    let gs ← getUnsolvedGoals
    for g in gs do
      let s ← saveState
      try
        let gs := gs.erase g
        let g ← renameInaccessibles g renameI
        setGoals (g :: gs)
        evalTactic <| ← `(tactic| refine_lift show $patt from ?_)
        -- This line should succeed:
        let g' :: gs' ← getUnsolvedGoals | throwNoGoalsToBeSolved
        return (g', gs')
      catch _ =>
        restoreState s
    throwError "No goals unify with the term {patt}"

elab_rules : tactic
  | `(tactic| case : $[$patts $[with $[$namess?]*]?]|* $[=>%$arr? $tac?]?) => do
    let stx ← getRef
    -- Accumulated goals in the no-`=>` case.
    let mut acc : List MVarId := []
    for patt in patts, names? in namess? do
      let (g, gs) ← showGoalOfPatt patt (names?.getD #[])
      if let (some arr, some tac) := (arr?, tac?) then
        setGoals (g :: gs)
        withCaseRef arr tac do
          closeUsingOrAdmit (withTacticInfoContext stx (evalTactic tac))
      else
        acc := g :: acc
        setGoals gs
    setGoals (acc.reverseAux (← getGoals))

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

/-- The body of a `case : ...` tactic. -/
syntax casePattBody := " => " (hole <|> syntheticHole <|> tacticSeq)

/--
* `case : t => tac` finds the first goal that unifies with `t` and then solves it
  using `tac` or else fails. Like `show`, it changes the type of the goal to `t`.

* `case : t with n₁ ... nₘ => tac` additionally names the `m` most recent hypotheses with
  inaccessible names to the given names. The names are renamed before matching against `t`.

* `case : t := e` is short for `case : t => exact e`.

* `case : t₁ | t₂ | ... => tac` is equivalent to `(case : t₁ => tac); (case : t₂ => tac); ...`
  but with all matching done on the original list of goals, in case pattern elaboration creates
  new goals.
  This supports `with` clauses as well for each pattern.

* `case : t` will make the matched goal be the first goal. `case : t₁ | t₂ | ...` makes the
  matched goals be the first goals in the given order.

* `case : t := _` and `case : t := ?m` are the same as `case : t` but in the `?m` case the
  goal tag is changed to `m`. In particular, the goal becomes metavariable `?m`.
-/
syntax (name := casePatt) "case" " : " sepBy1(casePattArg, " | ") (casePattBody)? : tactic

@[inherit_doc casePatt]
macro "case" " : " cs:sepBy1(casePattArg, " | ") " := " colGt t:term : tactic =>
  `(tactic| (case : $[$cs]|* => exact $t))

macro_rules
  | `(tactic| case : $[$cs:casePattArg]|*) => `(tactic| case : $[$cs]|* => _)

/-- Find the first goal whose type unifies with `patt`.
The `renameI` array consists of names to use to rename inaccessibles.
The `patt` term is elaborated in the context where the inaccessibles have been renamed.

Returns the found goal, goals caused by elaborating `patt`, and the remaining goals. -/
def findGoalOfPatt (gs : List MVarId) (patt : Term) (renameI : TSyntaxArray `Lean.binderIdent) :
    TacticM (MVarId × List MVarId × List MVarId) :=
  Term.withoutErrToSorry do
    for g in gs do
      let s ← saveState
      try
        let gs := gs.erase g
        let g ← renameInaccessibles g renameI
        let g' :: gs' ← run g do withoutRecover <|
                          evalTactic (← `(tactic| refine_lift show $patt from ?_))
          | throwNoGoalsToBeSolved -- This should not happen
        return (g', gs', gs)
      catch _ =>
        restoreState s
    throwError "No goals unify with the term {patt}, or too many names provided for renaming {
                ""}inaccessible variables."

/-- Given a `casePattBody`, either give a hole or a tactic sequence
(along with the syntax for the `=>`). -/
def processCasePattBody (stx : TSyntax ``casePattBody) :
    TacticM (Term ⊕ (Syntax × TSyntax ``Parser.Tactic.tacticSeq)) := do
  match stx with
  | `(casePattBody| => $t:hole) | `(casePattBody| => $t:syntheticHole) => return Sum.inl ⟨t⟩
  | `(casePattBody| =>%$arr $tac:tacticSeq) => return Sum.inr (arr, tac)
  | _ => throwUnsupportedSyntax

elab_rules : tactic
  | `(tactic| case : $[$patts $[with $[$namess?]*]?]|* $caseBody) => do
    let stx ← getRef
    let body ← processCasePattBody caseBody
    -- Accumulated goals in the hole cases.
    let mut acc : List MVarId := []
    -- Accumulated goals from refining patterns
    let mut pattref : List MVarId := []
    for patt in patts, names? in namess? do
      let (g, gs', gs) ← findGoalOfPatt (← getUnsolvedGoals) patt (names?.getD #[])
      setGoals gs
      pattref := pattref ++ gs'
      match body with
      | Sum.inl hole =>
        -- Copied from `induction` tactic. Elaborating the hole is how we can rename the goal tag.
        let gs' ← g.withContext <| withRef hole do
          let mvarDecl ← g.getDecl
          let val ← elabTermEnsuringType hole mvarDecl.type
          g.assign val
          let gs' ← getMVarsNoDelayed val
          tagUntaggedGoals mvarDecl.userName `case gs'.toList
          pure gs'
        acc := acc ++ gs'.toList
      | Sum.inr (arr, tac) =>
        discard <| run g do
          withCaseRef arr tac do
            closeUsingOrAdmit (withTacticInfoContext stx (evalTactic tac))
    setGoals (acc ++ pattref ++ (← getGoals))

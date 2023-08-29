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
For consistency with `case`, it takes a tag as well, but the tag can be a hole `_`.
-/

namespace Std.Tactic
open Lean Meta Elab Tactic

/-- Clause for a `case ... : ...` tactic. -/
syntax casePattArg := Parser.Tactic.caseArg (" : " term)?

/-- The body of a `case ... | ...` tactic that's a tactic sequence (or hole). -/
syntax casePattTac := " => " (hole <|> syntheticHole <|> tacticSeq)

/-- The body of a `case ... | ...` tactic that's an exact term. -/
syntax casePattExpr := " := " colGt term

/-- The body of a `case ... : ...` tactic. -/
syntax casePattBody := casePattTac <|> casePattExpr

/--
* `case _ : t => tac` finds the first goal that unifies with `t` and then solves it
  using `tac` or else fails. Like `show`, it changes the type of the goal to `t`.
  The `_` can optionally be a case tag, in which case it only looks at goals
  whose tag would be considered by `case` (goals with an exact tag match,
  followed by goals with the tag as a suffix, followed by goals with the tag as a prefix).

* `case _ n₁ ... nₘ : t => tac` additionally names the `m` most recent hypotheses with
  inaccessible names to the given names. The names are renamed before matching against `t`.
  The `_` can optionally be a case tag.

* `case _ : t := e` is short for `case _ : t => exact e`.

* `case _ : t₁ | _ : t₂ | ... => tac`
  is equivalent to `(case _ : t₁ => tac); (case _ : t₂ => tac); ...`
  but with all matching done on the original list of goals, in case pattern elaboration creates
  new goals.
  Each goal is consumed as they are matched, so patterns may repeat.

* `case _ : t` will make the matched goal be the first goal.
  `case _ : t₁ | _ : t₂ | ...` makes the matched goals be the first goals in the given order.

* `case _ : t := _` and `case _ : t := ?m` are the same as `case _ : t` but in the `?m` case the
  goal tag is changed to `m`.
  In particular, the goal becomes metavariable `?m`.
-/
-- Low priority so that type-free `case` doesn't conflict with core `case`,
-- though it should be a drop-in replacement.
syntax (name := casePatt) (priority := low)
  "case " sepBy1(casePattArg, " | ") (casePattBody)? : tactic

macro_rules
  | `(tactic| case $[$ps:casePattArg]|* := $t) => `(tactic| case $[$ps:casePattArg]|* => exact $t)
  | `(tactic| case $[$ps:casePattArg]|*) => `(tactic| case $[$ps:casePattArg]|* => _)

/-- Filter the `mvarIds` by tag. Returns those `MVarId`s that have `tag`
either as its user name, as a suffix of its user name, or as a prefix of its user name.
The results are sorted in this order.
This is like `Lean.Elab.Tactic.findTag?` but it returns all results. -/
private def filterTag (mvarIds : List MVarId) (tag : Name) : TacticM (List MVarId) := do
  let gs ← mvarIds.filterMapM fun mvarId => do
    let userName := (← mvarId.getDecl).userName
    if tag == userName then
      return some (0, mvarId)
    else if tag.isSuffixOf userName then
      return some (1, mvarId)
    else if tag.isPrefixOf userName then
      return some (2, mvarId)
    else
      return none
  -- Insertion sort is a stable sort:
  let gs := gs.toArray.insertionSort (·.1 < ·.1)
  return gs |>.map (·.2) |>.toList

/-- Find the first goal among those matching `tag` whose type unifies with `patt`.
The `renameI` array consists of names to use to rename inaccessibles.
The `patt` term is elaborated in the context where the inaccessibles have been renamed.

Returns the found goal, goals caused by elaborating `patt`, and the remaining goals. -/
def findGoalOfPatt (gs : List MVarId)
    (tag : TSyntax ``binderIdent) (patt? : Option Term) (renameI : TSyntaxArray `Lean.binderIdent) :
    TacticM (MVarId × List MVarId × List MVarId) :=
  Term.withoutErrToSorry do
    let gs ←
      match tag with
      | `($tag:ident) => filterTag gs tag.getId
      | _ => pure gs
    for g in gs do
      if let some patt := patt? then
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
      else
        return (g, [], gs.erase g)
    throwError "No goals with tag {tag} unify with the term {patt?.getD (← `(_))}, {
                ""}or too many names provided for renaming {
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
  | `(tactic| case $[$tags $hss* $[: $patts?]?]|* $caseBody) => do
    let stx ← getRef
    let body ← processCasePattBody caseBody
    -- Accumulated goals in the hole cases.
    let mut acc : List MVarId := []
    -- Accumulated goals from refining patterns
    let mut pattref : List MVarId := []
    for tag in tags, hs in hss, patt? in patts? do
      let (g, gs', gs) ← findGoalOfPatt (← getUnsolvedGoals) tag patt? hs
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

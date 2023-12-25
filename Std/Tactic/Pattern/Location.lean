/-
Copyright (c) 2023 Anand Rao Tadipatri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anand Rao Tadipatri
-/
import Lean.Elab.Term
import Lean.Elab.Tactic
import Lean.SubExpr

/-!

This file defines a `locs` syntax for tactic signatures to
refer to locations in the goal state.

This can be combined with patterns to define
tactics that target specific locations in the goal state.

This file is modelled on `Lean/Elab/Tactic/Location.lean`.

-/

open Lean Meta Elab Tactic

namespace Pattern.Location

/-- A hypothesis location can be
    - a wildcard, which refers to all hypotheses in the local context simultaneously
    - a specific hypothesis in the local context -/
syntax hypLoc := "at" ppSpace ("*" <|> ident)

/-- A value location refers to the body of a local `let` declaration. -/
syntax valLoc := "in" ppSpace ident

open Parser.Tactic.Conv in
/-- A location in the goal state with occurrences optionally specified. -/
syntax loc := ppSpace withPosition((hypLoc <|> valLoc) (occs)?)

/-- Occurrences at a goal location. This is similar to `SubExpr.GoalLocation`. -/
inductive GoalOccurrences
  /-- Occurrences in the type of a hypothesis. -/
  | hypType (fvarId : FVarId) (occs : Occurrences)
  /-- Occurrences in the value of a `let` hypothesis. -/
  | hypValue (fvarId : FVarId) (occs : Occurrences)
  /-- Occurrences in the target. -/
  | target (occs : Occurrences)
deriving Inhabited

open Parser Tactic Conv in
/-- Interpret `occs` syntax as `Occurrences`. -/
def expandOccs : Option (TSyntax ``occs) → Occurrences
  | none => .all
  | some occs =>
    match occs with
      | `(occs| (occs := *)) => .all
      | `(occs| (occs := $ids*)) => .pos <| ids.map TSyntax.getNat |>.toList
      | _ => panic! s!"Invalid syntax {occs} for occurrences."

/-- Interpret `loc` syntax as an array of `GoalOccurrences`. -/
def expandLoc : TSyntax ``loc → TacticM (Array GoalOccurrences)
  | `(loc| at * $[$_occs]?) => withMainContext do
    -- TODO: Maybe reverse the list of declarations, following `Lean/Elab/Tactic/Location.lean`
    (← getLCtx).decls.foldlM (init := #[.target .all]) fun goalOccs decl? => do
      match decl? with
      | some decl =>
        if decl.isImplementationDetail then
          return goalOccs
        else
          let goalOccs :=
            if decl.isLet then
              goalOccs.push <| .hypValue decl.fvarId .all
            else goalOccs
          return goalOccs.push <| .hypType decl.fvarId .all
      | none => return goalOccs
  | `(loc| at $hyp:ident $[$occs]?) => withMainContext do
    return #[.hypType (← getFVarId hyp) (expandOccs occs)]
  | `(loc| in $hyp:ident $[$occs]?) => withMainContext do
    return #[.hypValue (← getFVarId hyp) (expandOccs occs)]
  | _ => throwUnsupportedSyntax

end Pattern.Location


open Pattern.Location

/-- Substitute occurrences of a pattern in an expression with the result of `replacement`. -/
def substitute (e : Expr) (pattern : AbstractMVarsResult) (occs : Occurrences)
    (replacement : Expr → MetaM Expr) : MetaM Expr := do
  let (_, _, p) ← openAbstractMVarsResult pattern
  let eAbst ← kabstract e p occs
  unless eAbst.hasLooseBVars do
    throwError m!"Failed to find instance of pattern {indentExpr p} in {indentExpr e}."
  instantiateMVars <| Expr.instantiate1 eAbst (← replacement p)

/-- Replace the value of a local `let` hypothesis with `valNew`,
    which is assumed to be definitionally equal.

    This function is modified from `_root_.Lean.MVarId.replaceLocalDeclDefEq` in
    `Lean/Meta/Tactic/Replace.lean`. -/
def _root_.Lean.MVarId.replaceLocalLetDefEq (mvarId : MVarId) (fvarId : FVarId)
    (valNew : Expr) : MetaM MVarId := do
  mvarId.withContext do
    if valNew == (← fvarId.getValue?) then
      return mvarId
    else
      let mvarDecl ← mvarId.getDecl
      let lctxNew := (← getLCtx).modifyLocalDecl fvarId (·.setValue valNew)
      let mvarNew ← mkFreshExprMVarAt lctxNew (← getLocalInstances)
                      mvarDecl.type mvarDecl.kind mvarDecl.userName
      mvarId.assign mvarNew
      return mvarNew.mvarId!

/-- Replace a pattern at the specified locations with the value of `replacement`,
    which is assumed to be definitionally equal to the original pattern. -/
def replaceOccurrencesDefEq (locs : Array GoalOccurrences) (pattern : AbstractMVarsResult)
    (replacement : Expr → MetaM Expr) : TacticM Unit := withMainContext do
  let mut mvarId ← getMainGoal
  for loc in locs do
    match loc with
    | .hypType fvarId occs =>
      let hypType ← fvarId.getType
      mvarId ← mvarId.replaceLocalDeclDefEq fvarId <| ← substitute hypType pattern occs replacement
    | .hypValue fvarId occs =>
      let .some hypValue ← fvarId.getValue? |
        throwError m!"Hypothesis {fvarId.name} is not a `let`-declaration."
      mvarId ← mvarId.replaceLocalLetDefEq fvarId <| ← substitute hypValue pattern occs replacement
    | .target occs => do
      let targetType ← mvarId.getType
      mvarId ← mvarId.replaceTargetDefEq <| ← substitute targetType pattern occs replacement
  replaceMainGoal [mvarId]

/--
  Convert the given goal `Ctx |- target` into a goal containing `let userName : type := val`
    after the local declaration with if `fvarId`.
  It assumes `val` has type `type`, and that `type` is well-formed after `fvarId`.

  This is modelled on `Lean.MVarId.assertAfter`. -/
def Lean.MVarId.defineAfter (mvarId : MVarId) (fvarId : FVarId) (userName : Name)
    (type : Expr) (val : Expr) : MetaM AssertAfterResult := do
  mvarId.checkNotAssigned `defineAfter
  let (fvarIds, mvarId) ← mvarId.revertAfter fvarId
  let mvarId ← mvarId.define userName type val
  let (fvarIdNew, mvarId) ← mvarId.intro1P
  let (fvarIdsNew, mvarId) ← mvarId.introNP fvarIds.size
  let mut subst := {}
  for f in fvarIds, fNew in fvarIdsNew do
    subst := subst.insert f (mkFVar fNew)
  return { fvarId := fvarIdNew, mvarId, subst }

/-- Replace the value of the local `let` declaration `fvarId` with a new value `valNew`.

    This follows the code of `Lean.MVarId.replaceLocalDecl`. -/
def Lean.MVarId.replaceLocalLetDecl (mvarId : MVarId) (fvarId : FVarId) (valNew : Expr)
    : MetaM AssertAfterResult := mvarId.withContext do
  let localDecl ← fvarId.getDecl
  let (_, localDecl') ← findMaxFVar valNew |>.run localDecl
  let result ← mvarId.defineAfter localDecl'.fvarId localDecl.userName (← fvarId.getType) valNew
  (do let mvarIdNew ← result.mvarId.clear fvarId
      pure { result with mvarId := mvarIdNew })
    <|> pure result
where
  /-- The last free variable in the local context that occurs in the expression.

      This is essentially the same as the private definition `replaceLocalDeclCore.findMaxFVar`. -/
  findMaxFVar (e : Expr) : StateRefT LocalDecl MetaM Unit :=
    e.forEach' fun e => do
      if e.isFVar then
        let localDecl' ← e.fvarId!.getDecl
        modify fun localDecl => if localDecl'.index > localDecl.index then localDecl' else localDecl
        return false
      else
        return e.hasFVar

/-- Rewrite the equality term `heq` at the specified locations. -/
def replaceOccurrencesEq (locs : Array GoalOccurrences)
    (heq : Expr) (symm : Bool := false) : TacticM Unit := withMainContext do
  let mut mvarId ← getMainGoal
  let mut newGoals : List MVarId := []
  for loc in locs do
    match loc with
    | .hypType fvarId occs =>
      let hypType ← fvarId.getType
      let rwResult ← Term.withSynthesize <|
        mvarId.rewrite hypType heq symm (config := { occs := occs })
      mvarId := (← mvarId.replaceLocalDecl fvarId rwResult.eNew rwResult.eqProof).mvarId
      newGoals := newGoals ++ rwResult.mvarIds
    | .hypValue fvarId occs =>
      let .some hypValue ← fvarId.getValue? |
        throwError m!"Hypothesis {fvarId.name} is not a `let`-declaration."
      let rwResult ← Term.withSynthesize <|
        mvarId.rewrite hypValue heq symm (config := { occs := occs })
      mvarId := (← mvarId.replaceLocalLetDecl fvarId rwResult.eNew).mvarId
      newGoals := newGoals ++ rwResult.mvarIds
    | .target occs => do
      let targetType ← mvarId.getType
      let rwResult ← mvarId.rewrite targetType heq symm (config := { occs := occs })
      mvarId ← mvarId.replaceTargetEq rwResult.eNew rwResult.eqProof
      newGoals := newGoals ++ rwResult.mvarIds
  replaceMainGoal (mvarId :: newGoals)

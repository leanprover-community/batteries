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

/-- A hypothesis location with occurrences optionally specified.
    The location can either refer to the type of a local hypothesis or
    the body of a `let` declaration. -/
syntax hypLoc := ident <|> ("‹" ident ppSpace (Parser.Tactic.Conv.occs)? (ppSpace "in body")? "›")

/-- The `|-` or `⊢` pattern representing the goal. -/
syntax goalPattern := patternIgnore( atomic("|" noWs "-") <|> "⊢")

/-- The goal or target location with occurrences optionally specified. -/
syntax goalLoc := goalPattern <|> ("‹" goalPattern ppSpace Parser.Tactic.Conv.occs "›")

/-- The wildcard location which refers to all valid locations. -/
syntax wildcardLoc := "*"

/-- A list of locations in the goal state with occurrences optionally specified. -/
syntax locs := ppSpace withPosition("at" ppSpace (wildcardLoc <|> (hypLoc* (goalLoc)?)))

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

/-- Interpret `locs` syntax as an array of `GoalOccurrences`. -/
def expandLocs : TSyntax ``locs → TacticM (Array GoalOccurrences)
  | `(locs| at $_:wildcardLoc) => withMainContext do
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
  | `(locs| at $hyps* $[$goal?]?) => withMainContext do
    let hypOccs ← hyps.mapM expandHypLoc
    match goal? with
    | some goal => return hypOccs.push (expandGoalLoc goal)
    | none => return hypOccs
  | _ => throwUnsupportedSyntax
where
  /-- Interpret `hypLoc` syntax as `GoalOccurrences`. -/
  expandHypLoc : TSyntax ``hypLoc → TacticM GoalOccurrences
  | `(hypLoc| $hyp:ident) => withMainContext do
    return .hypType (← getFVarId hyp) .all
  | `(hypLoc| ‹$hyp:ident $[$occs]?›) => withMainContext do
    return .hypType (← getFVarId hyp) (expandOccs occs)
  | `(hypLoc| ‹$hyp $[$occs]? in body›) => withMainContext do
    return .hypValue (← getFVarId hyp) (expandOccs occs)
  |     _ => throwUnsupportedSyntax

  /-- Interpret `goalLoc` syntax as `GoalOccurrences`. -/
  expandGoalLoc : TSyntax ``goalLoc → GoalOccurrences
  | `(goalLoc| $_:goalPattern) => .target .all
  | `(goalLoc| ‹$_:goalPattern $occs›) => .target (expandOccs occs)
  | stx => panic! s!"Invalid syntax {stx} for goal location."

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

/-- Replace the value of the local `let` declaration `fvarId` with
    a new value `valNew` that is equal to the old one (witnessed by `eqProof`).

    This follows the code of `Lean.MVarId.replaceLocalDecl`. -/
def Lean.MVarId.replaceLocalLetDecl (mvarId : MVarId) (fvarId : FVarId) (valNew _eqProof : Expr)
    : MetaM AssertAfterResult := mvarId.withContext do
  let localDecl ← fvarId.getDecl
  let (_, localDecl') ← findMaxFVar valNew |>.run localDecl
  let result ← mvarId.defineAfter localDecl'.fvarId localDecl.userName (← fvarId.getType) valNew
  (do let mvarIdNew ← result.mvarId.clear fvarId
      pure { result with mvarId := mvarIdNew })
    <|> pure result
where
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
      mvarId := (← mvarId.replaceLocalLetDecl fvarId rwResult.eNew rwResult.eqProof).mvarId
      newGoals := newGoals ++ rwResult.mvarIds
    | .target occs => do
      let targetType ← mvarId.getType
      let rwResult ← mvarId.rewrite targetType heq symm (config := { occs := occs })
      mvarId ← mvarId.replaceTargetEq rwResult.eNew rwResult.eqProof
      newGoals := newGoals ++ rwResult.mvarIds
  replaceMainGoal (mvarId :: newGoals)

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

syntax hypTarget := ("at" <|> "in") ppSpace term
syntax goalTarget := "at" ppSpace patternIgnore( atomic("|" noWs "-") <|> "⊢")
syntax wildcardTarget := "at" ppSpace "*"

syntax loc := (Parser.Tactic.Conv.occs)? ppSpace (hypTarget <|> goalTarget)
syntax locs := withPosition(wildcardTarget <|> (ppSpace colGt loc)+)

inductive GoalOccurrences
  | hypType (fvarId : FVarId) (occs : Occurrences)
  | hypValue (fvarId : FVarId) (occs : Occurrences)
  | target (occs : Occurrences)

open Parser Tactic Conv in
/-- Expand syntax of type `occs` into `Occurrences`. -/
def expandOccs : Option (TSyntax ``occs) → Occurrences
  | none => .all
  | some occs =>
    match occs with
      | `(occs| (occs := *)) => .all
      | `(occs| (occs := $ids*)) => .pos <| ids.map TSyntax.getNat |>.toList
      | _ => panic! s!"Invalid syntax {occs} for occurrences."

open Parser Tactic Conv in
def expandLoc : TSyntax ``loc → TacticM GoalOccurrences
  | `(loc| $[$occs?]? at $hyp:term) => withMainContext do
    return .hypType (← getFVarId hyp) (expandOccs occs?)
  | `(loc| $[$occs?]? in $hyp:term) => withMainContext do
    return .hypValue (← getFVarId hyp) (expandOccs occs?)
  | `(loc| $[$occs?]? $_:goalTarget) => do
    return .target (expandOccs occs?)
  | _ => throwUnsupportedSyntax

def expandLocs : TSyntax ``locs → TacticM (Array GoalOccurrences)
  | `(locs| $_:wildcardTarget) => withMainContext do
    (← getLCtx).decls.foldlM (init := #[.target .all]) fun goalOccs decl? => do
      match decl? with
      | some decl =>
        let goalOccs :=
          if decl.isLet then
            goalOccs.push <| .hypValue decl.fvarId .all
          else goalOccs
        return goalOccs.push <| .hypType decl.fvarId .all
      | none => return goalOccs
  | `(locs| $[$locs]*) => locs.mapM expandLoc
  | _ => throwUnsupportedSyntax

end Pattern.Location

open Pattern.Location

def substitute (e : Expr) (pattern : AbstractMVarsResult) (occs : Occurrences) (replacement : Expr → MetaM Expr) : MetaM Expr := do
  let (_, _, p) ← openAbstractMVarsResult pattern
  let eAbst ← kabstract e p occs
  return Expr.instantiate1 eAbst (← replacement p)

-- modified from `Lean/Meta/Tactic/Replace/_root_.Lean.MVarId.replaceLocalDeclDefEq`
def _root_.Lean.MVarId.replaceLocalLetDefEq (mvarId : MVarId) (fvarId : FVarId) (valNew : Expr) : MetaM MVarId := do
  mvarId.withContext do
    if valNew == (← fvarId.getValue?) then
      return mvarId
    else
      let mvarDecl ← mvarId.getDecl
      let lctxNew := (← getLCtx).modifyLocalDecl fvarId (·.setValue valNew)
      let mvarNew ← mkFreshExprMVarAt lctxNew (← getLocalInstances) mvarDecl.type mvarDecl.kind mvarDecl.userName
      mvarId.assign mvarNew
      return mvarNew.mvarId!

def replaceOccurrencesDefEq (locs : Array GoalOccurrences)
    (pattern : AbstractMVarsResult) (replacement : Expr → MetaM Expr) : TacticM Unit := withMainContext do
  let mut mvarId ← getMainGoal
  for loc in locs do -- TODO: Get the `locs` in the right order (see `withLocation`) and filter out implementation details
    match loc with
    | .hypType fvarId occs =>
      let hypType ← fvarId.getType
      mvarId ← mvarId.replaceLocalDeclDefEq fvarId <| ← substitute hypType pattern occs replacement
    | .hypValue fvarId occs =>
      let .some hypValue ← fvarId.getValue? | throwError m!"Hypothesis {fvarId.name} is not a let-declaration."
      mvarId ← mvarId.replaceLocalLetDefEq fvarId <| ← substitute hypValue pattern occs replacement
    | .target occs => do
      let targetType ← mvarId.getType'
      mvarId ← mvarId.replaceTargetDefEq <| ← substitute targetType pattern occs replacement
  replaceMainGoal [mvarId]

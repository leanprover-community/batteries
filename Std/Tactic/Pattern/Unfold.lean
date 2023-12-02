/-
Copyright (c) 2023 J. W. Gerbscheid, Anand Rao Tadipatri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: J. W. Gerbscheid, Anand Rao Tadipatri
-/
import Lean
import Std.Tactic.Pattern.Utils

open Lean Meta MonadExceptOf Elab

/-!

# Targeted unfolding

An implementation of a tactic to unfold patterns at specified locations.

-/

section

/-- If the expression is a projection under binders, calculate the projection. -/
partial def reduceProjection (e : Expr) : ExceptT MessageData MetaM Expr :=
  e.withAppRev fun f revArgs => match f with
    | .proj _ i b => do
      let some value ← project? b i | throw m!"Could not project expression {b}."
      reduceProjection (value.betaRev revArgs)
    | _ => return e

/-- Replace a constant under binders by its definition (also taking care of let reductions). -/
def replaceByDefAux (e : Expr) : ExceptT MessageData MetaM Expr := do
  if let .letE _ _ v b _ := e then return b.instantiate1 v
  e.withAppRev fun f revArgs => match f with
    | .const name us => do
      let info ← getConstInfoDefn name
      let result := info.value.instantiateLevelParams info.levelParams us
      if ← isDefEq result f then
        reduceProjection (result.betaRev revArgs)
      else
        throw m!"Could not replace {f} by its definition."
    | _ => do
      let result ← reduceProjection (f.betaRev revArgs)
      if result == e then throw m!"Could not find a definition for {e}."
      else return result

/-- Replace the pattern by its definition at the specified occurrences in the expression. -/
def replaceByDef (e : Expr) (pattern : AbstractMVarsResult) (occs : Occurrences) : MetaM Expr := do
  let (_, _, p) ← openAbstractMVarsResult pattern
  let eAbst ← kabstract e p occs
  unless eAbst.hasLooseBVars do
    throwError m!"Failed to find instance of pattern {indentExpr p} in {indentExpr e}."
  match ← replaceByDefAux p with
  | .ok q =>
    let e' := eAbst.instantiate1 q
    instantiateMVars e'
  | .error err => throwError err

end

open Parser Tactic Conv in
/-- A tactic to perform targeted unfolding of patterns. -/
elab "unfold'" occs:(occs)? p:term loc:(location)? : tactic => withMainContext do
  let pattern ← expandPattern p
  let location := (expandLocation <$> loc).getD (.targets #[] true)
  let occurrences := expandOccs occs
  let goal ← getMainGoal
  goal.withContext do
    withLocation location
      (atLocal := fun fvarId ↦ do
        let hypType ← fvarId.getType
        let newGoal ← goal.replaceLocalDeclDefEq fvarId <| ←
          replaceByDef hypType pattern occurrences
        replaceMainGoal [newGoal])
      (atTarget := do
        let newGoal ← goal.replaceTargetDefEq <| ←
          replaceByDef (← goal.getType) pattern occurrences
        replaceMainGoal [newGoal])
      (failed := (throwTacticEx `unfold' · m!"Failed to unfold pattern {p}."))

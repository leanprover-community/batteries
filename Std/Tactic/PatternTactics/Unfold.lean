/-
Copyright (c) 2023 Jovan Gerbscheid, Anand Rao Tadipatri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jovan Gerbscheid, Anand Rao Tadipatri
-/
import Std.Tactic.Pattern.Utils
import Lean.Parser.Tactic

namespace Std.Tactic.Unfold
open Lean Meta Elab.Tactic Pattern

/-!
# Targeted unfolding

A tactic for definitionally unfolding expressions.
The targeted sub-expression is selected using a pattern.

-/

/-- Reduction function for the `unfold'` tactic. -/
def replaceByDef (e : Expr) : MetaM Expr :=
  withTransparency .all do
  /- β-reduction -/
  if e.isHeadBetaTarget then
    return e.withAppRev Expr.betaRev
  /- η-reduction -/
  if let some e := e.etaExpandedStrict? then
    return e
  /- ζ-reduction -/
  if let .letE _ _ v b _ := e then
    return b.instantiate1 v
  /- projection reduction -/
  if let some e ← reduceProj? e then
    return e.headBeta
  if let .const n _ := e.getAppFn then
    if ← isProjectionFn n then
      if let some e ← unfoldDefinition? e then
        if let some r ← reduceProj? e.getAppFn then
          return mkAppN r e.getAppArgs |>.headBeta
  /- unfolding a let-bound free variable -/
  if let .fvar fvarId := e.getAppFn then
    if let some value ← fvarId.getValue? then
      return value.betaRev e.getAppRevArgs
  /- unfolding a constant -/
  if let some e ← unfoldDefinition? e then
    return e

  throwError m! "Could not find a definition for {e}."


/-- Replace a pattern at the specified locations with the value of `replacement`,
    which is assumed to be definitionally equal to the original pattern. -/
def replaceOccurrencesDefEq (tacticName : Name) (pattern : Pattern.PatternLocation)
    (replacement : Expr → MetaM Expr) : TacticM Unit := do
  let mvarId ← getMainGoal
  mvarId.withContext do
    withLocation pattern.loc
      (atLocal := fun fvarId => do
        let hypType ← fvarId.getType
        let newGoal ← mvarId.replaceLocalDeclDefEq fvarId (← substitute hypType mvarId)
        replaceMainGoal [newGoal])
      (atTarget := do
        let newGoal ← mvarId.replaceTargetDefEq (← substitute (← mvarId.getType) mvarId)
        replaceMainGoal [newGoal])
      (failed := (throwTacticEx tacticName · ""))
where
  /-- Substitute occurrences of a pattern in an expression with the result of `replacement`. -/
  substitute (e : Expr) (mvarId : MVarId) : MetaM Expr := do
    let (_, _, p) ← openAbstractMVarsResult pattern.pattern
    let eAbst ← kabstract e p pattern.occurrences
    let p ← instantiateMVars p
    unless eAbst.hasLooseBVars do
      throwTacticEx tacticName mvarId
        "did not find instance of the pattern in the target expression{indendExpr p}"
    return eAbst.instantiate1 (← replacement p)

/-- Unfold the selected expression in one of the following ways:

- β-reduction: `(fun x₁ .. xₙ => t[x₁, .., xₙ]) a₁ .. aₙ` → `t[a₁, .., aₙ]`
- η-reduction: `fun x₁ .. xₙ => f x₁ .. xₙ` → `f`
- ζ-reduction: `let a := v; t[a]` → `t[v]`
- projection reduction: `instAddNat.1 a b` → `Nat.add a b`
- unfolding a constant or a let-bound free variable: `Surjective f` → `∀ b, ∃ a, f a = b`

Note that we always reduce a projection after unfolding a constant,
so that `@Add.add ℕ instAddNat a b` gives `Nat.add a b` instead of `instAddNat.1 a b`.
 -/
elab "unfold'" loc:patternLocation : tactic => withMainContext do
  let pattern ← expandPatternLocation loc
  replaceOccurrencesDefEq `unfold' pattern replaceByDef

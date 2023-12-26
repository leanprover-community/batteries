/-
Copyright (c) 2023 J. W. Gerbscheid, Anand Rao Tadipatri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: J. W. Gerbscheid, Anand Rao Tadipatri
-/
import Std.Tactic.Pattern.Utils

open Lean Meta

/-!

# Targeted unfolding

An implementation of a tactic to unfold patterns at specified locations.

-/

/-- If the head of the expression is a projection, reduce the projection. -/
def reduceProjection (e : Expr) : MetaM (Option Expr) := do
  let .proj _ i b := e.getAppFn | return none
  let some f ← project? b i | return none
  return f.betaRev e.getAppRevArgs

/-- Reduction function for the `unfold'` tactic. -/
def replaceByDef (e : Expr) : MetaM Expr := do
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
  if let some e ← reduceProjection e then
    return e
  /- unfolding a constant -/
  if let some e ← withTransparency .all <| unfoldDefinition? e then
    match ← reduceProjection e with
      | some e => return e
      | none => return e

  throwError m! "Could not find a definition for {e}."

open Elab.Tactic Pattern.Location

/-- Unfold the selected expression in one of the following ways:

- β-reduction: `(fun x₁ .. xₙ => t[x₁, .., xₙ]) a₁ .. aₙ` → `t[a₁, .., aₙ]`
- η-reduction: `fun x₁ .. xₙ => f x₁ .. xₙ` → `f`
- ζ-reduction: `let a := v; t[a]` → `t[v]`
- projection reduction: `instAddNat.1 a b` → `Nat.add a b`
- unfolding a constant: `Surjective f` → `∀ b, ∃ a, f a = b`

Note that we always reduce a projection after unfolding a constant,
so that `@Add.add ℕ instAddNat a b` gives `Nat.add a b` instead of `instAddNat.1 a b`.
 -/
elab "unfold'" "[" p:term "]" loc:loc : tactic => withMainContext do
  let pattern ← expandPattern p
  let occurrences ← expandLoc loc
  replaceOccurrencesDefEq occurrences pattern replaceByDef

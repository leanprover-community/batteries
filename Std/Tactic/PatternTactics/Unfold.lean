/-
Copyright (c) 2023 J. W. Gerbscheid, Anand Rao Tadipatri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: J. W. Gerbscheid, Anand Rao Tadipatri
-/
import Std.Tactic.Pattern.Utils
import Lean.Parser.Tactic

open Lean Meta

/-!

# Targeted unfolding

A tactic for definitionally unfolding expressions.
The targeted sub-expression is selected using a pattern.

example use case:
```
@[irreducible] def f (n : Nat) := n + 1
example : ∀ n : Nat, n + 1 = f n := by
  unfold' f _ at ⊢ --∀ (n : Nat), n + 1 = n + 1
  intro n
  rfl
```
-/

/-- If the head of the expression is a projection, reduce the projection. -/
def reduceHeadProjection (e : Expr) : MetaM (Option Expr) := do
  let .proj _ i b := e.getAppFn | return none
  let some f ← project? b i | return none
  return f.betaRev e.getAppRevArgs

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
  if let some e ← reduceHeadProjection e then
    return e
  /- unfolding a let-bound free variable -/
  if let .fvar fvarId := e.getAppFn then
    if let some value ← fvarId.getValue? then
      return value.betaRev e.getAppRevArgs
  /- unfolding a constant -/
  if let some e ← unfoldDefinition? e then
    match ← reduceHeadProjection e with
      | some e => return e
      | none => return e

  throwError m! "Could not find a definition for {e}."

open Elab Tactic Parser Tactic Conv

/-- Unfold the selected expression in one of the following ways:

- β-reduction: `(fun x₁ .. xₙ => t[x₁, .., xₙ]) a₁ .. aₙ` → `t[a₁, .., aₙ]`
- η-reduction: `fun x₁ .. xₙ => f x₁ .. xₙ` → `f`
- ζ-reduction: `let a := v; t[a]` → `t[v]`
- projection reduction: `instAddNat.1 a b` → `Nat.add a b`
- unfolding a constant or a let-bound free variable: `Surjective f` → `∀ b, ∃ a, f a = b`

Note that we always reduce a projection after unfolding a constant,
so that `@Add.add ℕ instAddNat a b` gives `Nat.add a b` instead of `instAddNat.1 a b`.
 -/
elab "unfold'" occs:(occs)? "[" p:term "]" loc:(location)? : tactic => withMainContext do
  let pattern ← expandPattern p
  let occurrences := expandOccs occs
  let location := (expandLocation <$> loc).getD (.targets #[] true)
  replaceOccurrencesDefEq `unfold' location occurrences pattern replaceByDef

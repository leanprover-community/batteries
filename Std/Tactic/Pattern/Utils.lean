/-
Copyright (c) 2023 Anand Rao Tadipatri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anand Rao Tadipatri
-/
import Lean

open Lean Meta Elab Tactic

/-!

Basic programming and meta-programming utilities for tactics that
target goal locations through patterns and their occurrences.

The code here include:
- Functions for expanding syntax for patterns and occurrences into their corresponding expressions
- Code for generating and finding the occurrences of patterns in expressions

The idea of referring to sub-expressions via patterns and occurrences is due to Yaël Dillies.

-/

section Expand

/-- Expand a term representing a pattern as an expression with meta-variables.
    This follows code from `Lean/Elab/Tactic/Conv/Pattern.lean`. -/
def expandPattern (p : Term) : TermElabM AbstractMVarsResult :=
  withTheReader Term.Context (fun ctx => { ctx with ignoreTCFailures := true }) <|
    Term.withoutModifyingElabMetaStateWithInfo <| withRef p <|
    Term.withoutErrToSorry do
      abstractMVars (← Term.elabTerm p none)

open Parser Tactic Conv in
/-- Expand syntax of type `occs` into `Occurrences`. -/
def expandOccs : Option (TSyntax ``occs) → Occurrences
  | none => .all
  | some occs =>
    match occs with
      | `(occs| (occs := *)) => .all
      | `(occs| (occs := $ids*)) => .pos <| ids.map TSyntax.getNat |>.toList
      | _ => panic! s!"Invalid syntax {occs} for occurrences."

end Expand

section PatternsAndOccurrences

/-- The pattern at a given position in an expression.
    Variables under binders are turned into meta-variables in the pattern. -/
def SubExpr.patternAt (p : SubExpr.Pos) (root : Expr) : MetaM Expr := do
  let e ← Core.viewSubexpr p root
  let binders ← Core.viewBinders p root
  let mvars ← binders.mapM fun (name, type) =>
    mkFreshExprMVar type (userName := name)
  return e.instantiateRev mvars

/-- Finds the occurrence number of the pattern in the expression
    that matches the sub-expression at the specified position.
    This follows the code of `kabstract` from Lean core. -/
def findMatchingOccurrence (position : SubExpr.Pos) (root : Expr) (pattern : Expr) : MetaM Nat := do
  let root ← instantiateMVars root
  unless ← isDefEq pattern (← SubExpr.patternAt position root) do
    throwError s!"The specified pattern does not match the pattern at position {position}."
  let pattern ← instantiateMVars pattern
  let pHeadIdx := pattern.toHeadIndex
  let pNumArgs := pattern.headNumArgs
  let rec
  /-- The recursive step in the expression traversal to search for matching occurrences. -/
  visit (e : Expr) (p : SubExpr.Pos) (offset : Nat) := do
    let visitChildren : Unit → StateRefT Nat (OptionT MetaM) Unit := fun _ => do
      match e with
      | .app f a         => do
        visit f p.pushAppFn offset <|>
        visit a p.pushAppArg offset
      | .mdata _ b       => visit b p offset
      | .proj _ _ b      => visit b p.pushProj offset
      | .letE _ t v b _  => do
        visit t p.pushLetVarType offset <|>
        visit v p.pushLetValue offset <|>
        visit b p.pushLetBody (offset+1)
      | .lam _ d b _     => do
        visit d p.pushBindingDomain offset <|>
        visit b p.pushBindingBody (offset+1)
      | .forallE _ d b _ => do
        visit d p.pushBindingDomain offset <|>
        visit b p.pushBindingBody (offset+1)
      | _                => failure
    if e.hasLooseBVars then
      visitChildren ()
    else if e.toHeadIndex != pHeadIdx || e.headNumArgs != pNumArgs then
      visitChildren ()
    else if (← isDefEq e pattern) then
      let i ← get
      set (i+1)
      if p = position then
        return ()
      else
        visitChildren ()
    else
      visitChildren ()
  let .some (_, occ) ← visit root .root 0 |>.run 0 |
    throwError s!"Could not find pattern at specified position {position}."
  return occ

/-- Finds the occurrence number of the pattern at
    the specified position in the whole expression. -/
def findOccurrence (position : SubExpr.Pos) (root : Expr) : MetaM Nat := do
  let pattern ← SubExpr.patternAt position root
  findMatchingOccurrence position root pattern

end PatternsAndOccurrences

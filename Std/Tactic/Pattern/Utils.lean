/-
Copyright (c) 2023 Anand Rao Tadipatri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anand Rao Tadipatri, Jovan Gerbscheid
-/
import Lean.Meta

namespace Std.Tactic.Pattern
open Lean Meta Elab Tactic Parser.Tactic Conv

/-!
We define the `patternLocation` syntax, which specifies one or more subexpressions
in the goal, using a pattern and an optional `occs` argument.
- The syntax is elaborated by `expandPatternLocation`
- The syntax can be created using `patternAndIndex`

-/

/-- Refer to a set of subexpression by specifying a pattern and occurrences.

For example, if hypothesis `h` says that `a + (b + c) = a + (b + c)`, then
`(occs := 2 3) _ + _ at h` refers to the two occurrences of `b + c`,
because it first skips `a + (b + c)`, and then matches with `b + c`,
which instantiates the pattern to be `b + c`, so the next match is the
second occurrence of `b + c`. -/
syntax patternLocation := (occs)? term (location)?


/-- A structure containing the information provided by the `patternLocation` syntax. -/
structure PatternLocation where
  /-- The occurences of the pattern in the target. -/
  occs : Option (Array Nat)
  /-- The pattern itself. -/
  pattern : AbstractMVarsResult
  /-- The location in the goal. -/
  loc : Location

/-- Get the pattern occurrences as a `Occurrences`. -/
def PatternLocation.occurrences (p : PatternLocation) : Occurrences :=
  match p.occs with
  | none => .all
  | some arr => .pos arr.toList

/-- Elaborate a pattern expression.
See elaboration of `Lean.Parser.Tactic.Conv.pattern`. -/
def expandPattern (p : Syntax) : TermElabM AbstractMVarsResult :=
  withReader (fun ctx => { ctx with ignoreTCFailures := true, errToSorry := false }) <|
    Term.withoutModifyingElabMetaStateWithInfo <| withRef p do
      abstractMVars (← Term.elabTerm p none)

/-- Elaborate `occs` syntax. -/
def expandOptOccs (stx : Option (TSyntax ``occs)) : TermElabM (Option (Array Nat)) := do
  let some stx := stx | return none
  match stx with
  | `(occs| (occs := *)) => return none
  | `(occs| (occs := $ids*)) =>
    some <$> ids.mapM fun id =>
      let n := id.toNat
      if n == 0 then
        throwErrorAt id "positive integer expected"
      else return n
  | _ => throwUnsupportedSyntax

/-- Elaborate `patternLocation` syntax. -/
def expandPatternLocation (stx : Syntax) : TacticM PatternLocation :=
  withMainContext do
  match stx with
  | `(patternLocation| $[$a]? $pat $[$loc]?) =>
    let occs ← expandOptOccs a
    let pattern ← expandPattern pat
    let loc := match loc with
      | some loc => expandLocation loc
      | none => Location.targets #[] true
    return { occs, pattern, loc }
  | _ => throwUnsupportedSyntax


/-- Return the subexpression positions that `kabstract` can abstract, in order of traversal -/
def kabstractPositions (p e : Expr) : MetaM (Array SubExpr.Pos) := do
  let pHeadIdx := p.toHeadIndex
  let pNumArgs := p.headNumArgs
  let rec
  /-- The recursive step in the expression traversal to search for matching occurrences. -/
  visit (e : Expr) (pos : SubExpr.Pos) (positions : Array SubExpr.Pos) :
      MetaM (Array SubExpr.Pos) := do
    let visitChildren : Array SubExpr.Pos → MetaM (Array SubExpr.Pos) :=
      match e with
      | .app f a         => visit f pos.pushAppFn
                        >=> visit a pos.pushAppArg
      | .mdata _ b       => visit b pos
      | .proj _ _ b      => visit b pos.pushProj
      | .letE _ t v b _  => visit t pos.pushLetVarType
                        >=> visit v pos.pushLetValue
                        >=> visit b pos.pushLetBody
      | .lam _ d b _     => visit d pos.pushBindingDomain
                        >=> visit b pos.pushBindingBody
      | .forallE _ d b _ => visit d pos.pushBindingDomain
                        >=> visit b pos.pushBindingBody
      | _                => pure
    if e.hasLooseBVars || e.toHeadIndex != pHeadIdx || e.headNumArgs != pNumArgs then
      visitChildren positions
    else
      let mctx ← getMCtx
      if (← isDefEq e p) then
        setMCtx mctx
        visitChildren (positions.push pos)
      else
        visitChildren positions
  visit e .root #[]

/-- Return the pattern and occurrences specifying position `pos` in target `e`. -/
def patternAndIndex (pos : SubExpr.Pos) (e : Expr) : MetaM (Expr × Option Nat) := do
  let e ← instantiateMVars e
  let pattern ← Core.viewSubexpr pos e
  if pattern.hasLooseBVars then
    throwError "the subexpression contains loose bound variables"
  let positions ← kabstractPositions pattern e
  if positions.size == 1 then
    return (pattern, none)
  let some index := positions.findIdx? (· == pos) | unreachable!
  return (pattern, some (index + 1))

/-
Copyright (c) 2023 J. W. Gerbscheid, Anand Rao Tadipatri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: J. W. Gerbscheid, Anand Rao Tadipatri
-/
import Std.Tactic.Pattern.Utils

open Lean Meta MonadExceptOf Elab

/-!

# Targeted unfolding

An implementation of a tactic to unfold patterns at specified locations.

-/

/-- If the expression is a projection under binders, calculate the projection. -/
partial def reduceProjection (e : Expr) : MetaM Expr :=
  e.withAppRev fun f revArgs =>
    match f with
    | .proj _ i b => do
      let some value ← project? b i | throwError m!"Could not project expression {b}."
      reduceProjection (value.betaRev revArgs)
    | _ => return e

/-- Replace a constant under binders by its definition (also taking care of let reductions). -/
def replaceByDef (e : Expr) : MetaM Expr := do
  if let .letE _ _ v b _ := e then return b.instantiate1 v
  e.withAppRev fun f revArgs => match f with
    | .const name us => do
      let info ← getConstInfoDefn name
      let result := info.value.instantiateLevelParams info.levelParams us
      if ← isDefEq result f then
        reduceProjection (result.betaRev revArgs)
      else
        throwError m!"Could not replace {f} by its definition."
    | _ => do
      let result ← reduceProjection (f.betaRev revArgs)
      if result == e then throwError m!"Could not find a definition for {e}."
      else return result

open Parser Tactic Conv Pattern Location in
/-- A tactic to perform targeted unfolding of patterns. -/
elab "unfold'" p:term locs:locs : tactic => withMainContext do
  let pattern ← expandPattern p
  let occurrences ← expandLocs locs
  replaceOccurrencesDefEq occurrences pattern replaceByDef

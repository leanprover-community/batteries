/-
Copyright (c) 2023 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Std.Lean.Meta.Basic
import Std.Lean.Expr
import Lean.Elab.Tactic.ElabTerm

/-!
# `let_projs`

`let_projs` adds let bindings for all projections of local hypotheses, recursively.

It should not be used interactively,
but may be useful as a preprocessing step for tactics such as `solve_by_elim`.
-/

open Lean Meta

namespace Std.Tactic.LetProjs

/--
Builds all the projections of an expression,
returning an array of pairs consisting of the projection name
and the projection applied to the original expression.
-/
def allProjs (e : Expr) : MetaM (Array (Name × Expr)) := do
  let (c, _) := (← inferType e).getAppFnArgs
  let env ← getEnv
  unless isStructure env c do return #[]
  (getStructureFields env c).filterMapM fun f => return (f, ← mkProjection e f)

/--
Add to the local context all projections of an expression,
naming them all with a prefix `h` followed by the projection name.
-/
def letAllProjs (e : Expr) (h : Name) (g : MVarId) :
    MetaM (MVarId × Array FVarId) := g.withContext do
  let mut r := #[]
  let mut g := g
  for ⟨n, p⟩ in ← allProjs e do
    let n' := h.appendAfter ("_" ++ n.toString)
    let ⟨h', g'⟩ ← g.«let» n' p
    g := g'
    r := r.push h'
  return (g, r)

/--
Add to the local context all projections of a local variable,
and then all projections of these results, and so on.

(If `e` is not of the form `.fvar h`, does nothing.)
-/
partial def letAllProjsRec (e : Expr) (g : MVarId) : MetaM MVarId := g.withContext do
  if let .fvar h := e then
    let (g', new) ← letAllProjs e (← h.getDecl).userName g
    new.foldlM (init := g') fun g h => letAllProjsRec (.fvar h) g
  else
    pure g

/--
`letProjs` adds let bindings for all projections of the specified hypotheses.
-/
def _root_.Lean.MVarId.letProjs (g : MVarId) (hs : Array FVarId) : MetaM MVarId := do
  hs.foldlM (init := g) fun g h => letAllProjsRec (.fvar h) g

/--
`letProjsAll` adds let bindings for all projections of all hypotheses.
-/
def _root_.Lean.MVarId.letProjsAll (g : MVarId) : MetaM MVarId := g.withContext do
  g.letProjs ((← getLocalHyps).map Expr.fvarId!)

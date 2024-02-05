/-
Copyright (c) 2023 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Std.Lean.Meta.Basic
import Std.Lean.Expr
import Lean.Elab.Tactic.ElabTerm

/-!
# `Lean.MVarId.haveProjs`

`haveProjs` adds hypotheses for all projections of specified local hypotheses, recursively.
`haveProjsAll` does so for all local hypotheses except instances
(unless invoked as `haveProjsAll (instances := true)`)

It is typicall not useful interactively (so there is no syntactical frontend)
but may be useful as a preprocessing step for tactics such as `solve_by_elim`.
-/

open Lean Meta

namespace Std.Tactic.HaveProjs

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
def haveAllProjs (e : Expr) (h : Name) (g : MVarId) :
    MetaM (MVarId × Array FVarId) := g.withContext do
  let mut r := #[]
  let mut g := g
  for ⟨n, p⟩ in ← allProjs e do
    let n' := h.appendAfter ("_" ++ n.toString)
    let ⟨h', g'⟩ ← g.note n' p
    g := g'
    r := r.push h'
  return (g, r)

/--
Add to the local context all projections of a local variable,
and then all projections of these results, and so on.

(If `e` is not of the form `.fvar h`, does nothing.)
-/
partial def haveAllProjsRec (e : Expr) (g : MVarId) : MetaM MVarId :=
  g.withContext do
    if let .fvar h := e then
      let (g', new) ← haveAllProjs e (← h.getDecl).userName g
      new.foldlM (init := g') fun g h => haveAllProjsRec (.fvar h) g
    else
      pure g

end Std.Tactic.HaveProjs

open Std.Tactic.HaveProjs

/--
`haveProjs` adds new hypotheses for all projections of the specified hypotheses.
-/
def Lean.MVarId.haveProjs (g : MVarId) (hs : Array FVarId) : MetaM MVarId := do
  hs.foldlM (init := g) fun g h => haveAllProjsRec (.fvar h) g

/--
`haveProjsAll` adds new hypotheses for all projections of all hypotheses.

By default does not add projections for instances.
-/
def Lean.MVarId.haveProjsAll (g : MVarId) (instances := false) : MetaM MVarId := g.withContext do
  let hyps := ((← getLocalHyps).map Expr.fvarId!)
  let filtered ← if instances then
    pure hyps
  else
    hyps.filterM fun h => do pure (← isClass? (← h.getType)).isNone
  g.haveProjs filtered

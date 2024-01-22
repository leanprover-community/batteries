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

/--
Analogue of `Lean.getStructureFields`,
but return an empty array rather than panicking if `structName` does not refer to a structure.
-/
def Lean.getStructureFields! (env : Environment) (structName : Name) : Array Name :=
  if let some info := getStructureInfo? env structName then
    info.fieldNames
  else
    #[]

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
  (getStructureFields! env c).filterMapM fun f => return (f, ← mkProjection e f)

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

open Elab Tactic

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


/--
`let_projs` adds let bindings for all projections of local hypotheses, recursively.

For example in
```
example (x : Nat × Nat × Nat) : True := by
  let_projs
  trivial
```
we have
```
x_fst: ℕ := x.1
x_snd: ℕ × ℕ := x.2
x_snd_fst: ℕ := x_snd.1
x_snd_snd: ℕ := x_snd.2
```

`let_projs h₁ h₂` only adds let bindings for projections of the specified hypotheses.
-/
syntax (name := let_projs_syntax) "let_projs" (ppSpace colGt ident)* : tactic

@[inherit_doc let_projs_syntax]
elab_rules : tactic | `(tactic| let_projs $hs:ident*) => do
  let hs ← getFVarIds hs
  if hs.isEmpty then
    liftMetaTactic fun g => return [← g.letProjsAll]
  else
    liftMetaTactic fun g => return [← g.letProjs hs]

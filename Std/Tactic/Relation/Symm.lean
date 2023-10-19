/-
Copyright (c) 2022 Siddhartha Gadgil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Siddhartha Gadgil, Mario Carneiro, Scott Morrison
-/
import Std.Lean.Meta.Basic

/-!
# `symm` tactic

This implements the `symm` tactic, which can apply symmetry theorems to either the goal or a
hypothesis.
-/

set_option autoImplicit true

open Lean Meta

namespace Std.Tactic

/-- Environment extensions for symm lemmas -/
initialize symmExt :
    SimpleScopedEnvExtension (Name × Array (DiscrTree.Key true)) (DiscrTree Name true) ←
  registerSimpleScopedEnvExtension {
    addEntry := fun dt (n, ks) => dt.insertCore ks n
    initial := {}
  }

initialize registerBuiltinAttribute {
  name := `symm
  descr := "symmetric relation"
  add := fun decl _ kind => MetaM.run' do
    let declTy := (← getConstInfo decl).type
    let (xs, _, targetTy) ← withReducible <| forallMetaTelescopeReducing declTy
    let fail := throwError
      "@[symm] attribute only applies to lemmas proving x ∼ y → y ∼ x, got {declTy}"
    let some _ := xs.back? | fail
    let targetTy ← reduce targetTy
    let .app (.app rel _) _ := targetTy | fail
    let key ← withReducible <| DiscrTree.mkPath rel
    symmExt.add (decl, key) kind
}

end Std.Tactic

open Std.Tactic

namespace Lean.Expr

/--
Internal implementation of `Lean.Expr.applySymm`, `Lean.MVarId.applySymm`,
and the user-facing tactic.

`tgt` should be of the form `a ~ b`, and is used to index the symm lemmas.

`k lem args body` should calculate a result,
given a candidate `symm` lemma `lem`, which will have type `∀ args, body`.

In `Lean.Expr.applySymm` this result will be a new `Expr`,
and in `Lean.MVarId.applySymm` and `Lean.MVarId.applySymmAt` this result will be a new goal.
-/
-- This function is rather opaque, but the design with a generic continuation `k`
-- is necessary in order to factor out all the common requirements below.
private def applySymmAux (tgt : Expr) (k : Expr → Array Expr → Expr → MetaM α) : MetaM α := do
  let .app (.app rel _) _ := tgt
    | throwError "symmetry lemmas only apply to binary relations, not{indentExpr tgt}"
  for lem in ← (symmExt.getState (← getEnv)).getMatch rel do
    try
      let lem ← mkConstWithFreshMVarLevels lem
      let (args, _, body) ← withReducible <| forallMetaTelescopeReducing (← inferType lem)
      return (← k lem args body)
    catch _ => pure ()
  throwError "no applicable symmetry lemma found for{indentExpr tgt}"

/-- Given a term `e : a ~ b`, construct a term in `b ~ a` using `@[symm]` lemmas. -/
def applySymm (e : Expr) : MetaM Expr := do
  applySymmAux (← instantiateMVars (← inferType e)) fun lem args body => do
    let .true ← isDefEq args.back e | failure
    mkExpectedTypeHint (mkAppN lem args) (← instantiateMVars body)

end Lean.Expr

namespace Lean.MVarId

/--
Internal implementation of `Lean.MVarId.applySymm` and the user-facing tactic.

`tgt` should be of the form `a ~ b`, and is used to index the symm lemmas.

`k lem args body goal` should transform `goal` into a new goal,
given a candidate `symm` lemma `lem`, which will have type `∀ args, body`.
Depending on whether we are working on a hypothesis or a goal,
`k` will internally use either `replace` or `assign`.
-/
private def applySymmAux
    (tgt : Expr) (k : Expr → Array Expr → Expr → MVarId → MetaM MVarId) (g : MVarId) :
    MetaM MVarId := do
  tgt.applySymmAux fun lem args body => do
    let g' ← k lem args body g
    g'.setTag (← g.getTag)
    return g'

/-- Apply a symmetry lemma (i.e. marked with `@[symm]`) to a metavariable. -/
def applySymm (g : MVarId) : MetaM MVarId := do
  g.applySymmAux (← g.getTypeCleanup) fun lem args body g => do
    let .true ← isDefEq (← g.getType) body | failure
    g.assign (mkAppN lem args)
    return args.back.mvarId!

/-- Use a symmetry lemma (i.e. marked with `@[symm]`) to replace a hypothesis in a goal. -/
def applySymmAt (h : FVarId) (g : MVarId) : MetaM MVarId := do
  let h' ← (Expr.fvar h).applySymm
  pure (← g.replace h h').mvarId

end Lean.MVarId

namespace Std.Tactic

open Lean.Elab.Tactic

/--
* `symm` applies to a goal whose target has the form `t ~ u` where `~` is a symmetric relation,
  that is, a relation which has a symmetry lemma tagged with the attribute [symm].
  It replaces the target with `u ~ t`.
* `symm at h` will rewrite a hypothesis `h : t ~ u` to `h : u ~ t`.
-/
elab "symm" loc:((Parser.Tactic.location)?) : tactic =>
  let atHyp h := liftMetaTactic1 fun g => g.applySymmAt h
  let atTarget := liftMetaTactic1 fun g => g.applySymm
  withLocation (expandOptLocation loc) atHyp atTarget fun _ => throwError "symm made no progress"

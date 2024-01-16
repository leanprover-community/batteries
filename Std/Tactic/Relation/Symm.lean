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

/-- Discrimation tree settings for the `symm` extension. -/
def symmExt.config : WhnfCoreConfig := {}

/-- Environment extensions for symm lemmas -/
initialize symmExt :
    SimpleScopedEnvExtension (Name × Array DiscrTree.Key) (DiscrTree Name) ←
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
    let key ← withReducible <| DiscrTree.mkPath rel symmExt.config
    symmExt.add (decl, key) kind
}

end Std.Tactic

open Std.Tactic

namespace Lean.Expr

/-- Return the symmetry lemmas that match the target type. -/
def getSymmLems (tgt : Expr) : MetaM (Array Name) := do
  let .app (.app rel _) _ := tgt
    | throwError "symmetry lemmas only apply to binary relations, not{indentExpr tgt}"
  (symmExt.getState (← getEnv)).getMatch rel symmExt.config

/-- Given a term `e : a ~ b`, construct a term in `b ~ a` using `@[symm]` lemmas. -/
def applySymm (e : Expr) : MetaM Expr := do
  let tgt <- instantiateMVars (← inferType e)
  let lems ← getSymmLems tgt
  let s ← saveState
  let act lem := do
        restoreState s
        let lem ← mkConstWithFreshMVarLevels lem
        let (args, _, body) ← withReducible <| forallMetaTelescopeReducing (← inferType lem)
        let .true ← isDefEq args.back e | failure
        mkExpectedTypeHint (mkAppN lem args) (← instantiateMVars body)
  lems.toList.firstM act
    <|> throwError m!"no applicable symmetry lemma found for {indentExpr tgt}"

end Lean.Expr


namespace Lean.MVarId

/--
Apply a symmetry lemma (i.e. marked with `@[symm]`) to a metavariable.

The type of `g` should be of the form `a ~ b`, and is used to index the symm lemmas.
-/
def applySymm (g : MVarId) : MetaM MVarId := do
  let tgt <- g.getTypeCleanup
  let lems ← Expr.getSymmLems tgt
  let act lem : MetaM MVarId := do
        let lem ← mkConstWithFreshMVarLevels lem
        let (args, _, body) ← withReducible <| forallMetaTelescopeReducing (← inferType lem)
        let .true ← isDefEq (← g.getType) body | failure
        g.assign (mkAppN lem args)
        let g' := args.back.mvarId!
        g'.setTag (← g.getTag)
        pure g'
  lems.toList.firstM act
    <|> throwError m!"no applicable symmetry lemma found for {indentExpr tgt}"

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

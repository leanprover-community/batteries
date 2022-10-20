/-
Copyright (c) 2021 Gabriel Ebner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner, Mario Carnteiro
-/
import Std.Tactic.Basic
import Std.Tactic.RCases
import Std.Lean.Command
import Lean

namespace Std.Tactic.Ext
open Lean Meta

/-- `declare_ext_theorems_for A` declares the extensionality theorems for `A`. -/
syntax "declare_ext_theorems_for" ident : command

/-- The environment extension to track `@[ext]` lemmas. -/
initialize extExtension : SimpleScopedEnvExtension (Name × Array DiscrTree.Key) (DiscrTree Name) ←
  registerSimpleScopedEnvExtension {
    addEntry := fun dt (n, ks) => dt.insertCore ks n
    initial := {}
  }

/-- Get the list of `@[ext]` lemmas corresponding to the key `ty`. -/
@[inline] def getExtLemmas (ty : Expr) : MetaM (Array Name) := do
  (extExtension.getState (← getEnv)).getMatch ty

initialize registerBuiltinAttribute {
  name := `ext
  descr := "Marks a lemma as extensionality lemma"
  add := fun decl _stx kind => do
    if isStructure (← getEnv) decl then
      liftCommandElabM <| Elab.Command.elabCommand <|
        ← `(declare_ext_theorems_for $(mkIdent decl))
    else MetaM.run' do
      let declTy := (← getConstInfo decl).type
      let (_, _, declTy) ← withDefault <| forallMetaTelescopeReducing declTy
      let failNotEq := throwError
        "@[ext] attribute only applies to structures or lemmas proving x = y, got {declTy}"
      let some (ty, lhs, rhs) := declTy.eq? | failNotEq
      unless lhs.isMVar && rhs.isMVar do failNotEq
      let key ←
        if (← withReducible <| whnf ty).isForall then
          pure #[.star] -- FIXME: workaround
        else
          withReducible <| DiscrTree.mkPath ty
      extExtension.add (decl, key) kind }

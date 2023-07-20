/-
Copyright (c) 2021 Gabriel Ebner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner, Mario Carneiro
-/
import Std.Tactic.RCases
import Std.Lean.Command

namespace Std.Tactic.Ext
open Lean Meta

/-- `declare_ext_theorems_for A` declares the extensionality theorems for the structure `A`. -/
syntax "declare_ext_theorems_for " ("(" &"flat" " := " term ") ")? ident (ppSpace prio)? : command

/-- Information about an extensionality theorem, stored in the environment extension. -/
structure ExtTheorem where
  /-- Declaration name of the extensionality theorem. -/
  declName : Name
  /-- Priority of the extensionality theorem. -/
  priority : Nat
  /-- Key in the discrimination tree. -/
  keys : Array (DiscrTree.Key true)
  deriving Inhabited, Repr, BEq, Hashable

/-- The environment extension to track `@[ext]` lemmas. -/
initialize extExtension :
    SimpleScopedEnvExtension ExtTheorem (DiscrTree ExtTheorem true) ←
  registerSimpleScopedEnvExtension {
    addEntry := fun dt thm => dt.insertCore thm.keys thm
    initial := {}
  }

/-- Get the list of `@[ext]` lemmas corresponding to the key `ty`,
ordered from high priority to low. -/
@[inline] def getExtLemmas (ty : Expr) : MetaM (Array ExtTheorem) :=
  -- Using insertion sort because it is stable and the list of matches should be mostly sorted.
  -- Most ext lemmas have default priority.
  return (← (extExtension.getState (← getEnv)).getMatch ty)
    |>.insertionSort (·.priority < ·.priority) |>.reverse

/-- Registers an extensionality lemma.

* When `@[ext]` is applied to a structure, it generates `.ext` and `.ext_iff` theorems and registers
  them for the `ext` tactic.

* When `@[ext]` is applied to a theorem, the theorem is registered for the `ext` tactic.

* You can use `@[ext 9000]` to specify a priority for the attribute.

* You can use the flag `@[ext (flat := false)]` to prevent flattening all fields of parent
  structures in the generated extensionality lemmas. -/
syntax (name := ext) "ext" (" (" &"flat" " := " term ")")? (ppSpace prio)? : attr

initialize registerBuiltinAttribute {
  name := `ext
  descr := "Marks a lemma as extensionality lemma"
  add := fun declName stx kind => do
    let `(attr| ext $[(flat := $f)]? $(prio)?) := stx
      | throwError "unexpected @[ext] attribute {stx}"
    if isStructure (← getEnv) declName then
      liftCommandElabM <| Elab.Command.elabCommand <|
        ← `(declare_ext_theorems_for $[(flat := $f)]? $(mkCIdentFrom stx declName) $[$prio]?)
    else MetaM.run' do
      if let some flat := f then
        throwErrorAt flat "unexpected 'flat' config on @[ext] lemma"
      let declTy := (← getConstInfo declName).type
      let (_, _, declTy) ← withDefault <| forallMetaTelescopeReducing declTy
      let failNotEq := throwError
        "@[ext] attribute only applies to structures or lemmas proving x = y, got {declTy}"
      let some (ty, lhs, rhs) := declTy.eq? | failNotEq
      unless lhs.isMVar && rhs.isMVar do failNotEq
      let keys ← withReducible <| DiscrTree.mkPath ty
      let priority ← liftCommandElabM do Elab.liftMacroM do
        evalPrio (prio.getD (← `(prio| default)))
      extExtension.add {declName, keys, priority} kind
}

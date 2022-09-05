/-
Copyright (c) 2022 Gabriel Ebner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner, Mario Carneiro
-/
import Lean.PrettyPrinter.Delaborator.Builtins
open Lean Meta Std

namespace Tactic.NormCast

/-- The different types of coercions that are supported by the `coe` attribute. -/
inductive CoeFnType
  | /-- The basic coercion `↑x`, see `CoeT.coe` -/
    coe
  | /-- The coercion to a function type, see `CoeFun.coe` -/
    coeFun
  | /-- The coercion to a type, see `CoeSort.coe` -/
    coeSort
  deriving Inhabited, Repr, DecidableEq

instance : ToExpr CoeFnType where
  toTypeExpr := mkConst ``CoeFnType
  toExpr := open CoeFnType in fun
    | coe => mkConst ``coe
    | coeFun => mkConst ``coeFun
    | coeSort => mkConst ``coeSort

/-- Information associated to a coercion function to enable sensible delaboration. -/
structure CoeFnInfo where
  /-- The number of arguments to the coercion function -/
  numArgs : Nat
  /-- The argument index that represents the value being coerced -/
  coercee : Nat
  /-- The type of coercion -/
  type : CoeFnType
  deriving Inhabited, Repr

instance : ToExpr CoeFnInfo where
  toTypeExpr := mkConst ``CoeFnInfo
  toExpr | ⟨a, b, c⟩ => mkApp3 (mkConst ``CoeFnInfo.mk) (toExpr a) (toExpr b) (toExpr c)

/-- The environment extension for tracking coercion functions for delaboration -/
initialize coeExt : SimpleScopedEnvExtension (Name × CoeFnInfo) (NameMap CoeFnInfo) ←
  registerSimpleScopedEnvExtension {
    name := `coe
    addEntry := fun st (n, i) => st.insert n i
    initial := {}
  }

/-- Lookup the coercion information for a given function -/
def getCoeFnInfo? (fn : Name) : CoreM (Option CoeFnInfo) :=
  return (coeExt.getState (← getEnv)).find? fn

open PrettyPrinter.Delaborator SubExpr

/--
This delaborator tries to elide functions which are known coercions.
For example, `Int.ofNat` is a coercion, so instead of printing `ofNat n` we just print `n`,
and when re-parsing this we can (usually) recover the fact that the coercion function
should be inserted.
-/
def coeDelaborator (info : CoeFnInfo) : Delab := whenPPOption getPPCoercions do
  match info.type with
  | CoeFnType.coeFun =>
    unless (← getExpr).getAppNumArgs > info.numArgs do failure
    let coercee ← withNaryArg info.coercee delab
    let kinds ← getParamKinds
    let mut args := #[]
    for i in [info.numArgs:kinds.size] do
      if (kinds.get? i).all (·.bInfo.isExplicit) then
        args := args.push (← withNaryArg i delab)
    if args.isEmpty then failure
    `($coercee $args*)
  | _ =>
    unless (← getExpr).getAppNumArgs == info.numArgs do failure
    let coercee ← withNaryArg info.coercee delab
    `(↑ $coercee)

/-- Add a coercion delaborator for the given function. -/
def addCoeDelaborator (name : Name) (info : CoeFnInfo) : MetaM Unit := do
  let delabName := name ++ `delaborator
  addAndCompile <| Declaration.defnDecl {
    name := delabName
    levelParams := []
    type := mkConst ``Delab
    value := mkApp (mkConst ``coeDelaborator) (toExpr info)
    hints := .opaque
    safety := .safe
  }
  let kind := `app ++ name
  Attribute.add delabName `delab (Unhygienic.run `(attr| delab $(mkIdent kind):ident))

/-- Add `name` to the coercion extension and add a coercion delaborator for the function. -/
def registerCoercion (name : Name) (info : Option CoeFnInfo := none) : MetaM Unit := do
  let info ← match info with | some info => pure info | none => do
    let fnInfo ← getFunInfo (← mkConstWithLevelParams name)
    unless fnInfo.getArity > 0 do throwError "{name} not of function type"
    pure { numArgs := fnInfo.getArity, coercee := fnInfo.getArity - 1, type := .coe }
  modifyEnv (coeExt.addEntry · (name, info))
  addCoeDelaborator name info

/--
The `@[coe]` attribute on a function (which should also appear in a
`instance : Coe A B := ⟨myFn⟩` declaration) allows the delaborator to elide
applications of this function when printing expressions.
-/
syntax (name := Attr.coe) "coe" : attr

initialize registerBuiltinAttribute {
  name := `coe
  descr := "Adds a definition as a coercion"
  add := fun decl _stx kind => MetaM.run' do
    unless kind == .global do
      throwError "cannot add local or scoped coe attribute"
    registerCoercion decl
}

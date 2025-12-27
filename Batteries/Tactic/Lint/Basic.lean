/-
Copyright (c) 2020 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Robert Y. Lewis, Gabriel Ebner
-/
module

public meta import Lean.Structure
public meta import Lean.Elab.InfoTree.Main
public meta import Lean.Elab.Exception

public meta section

open Lean Meta

namespace Batteries.Tactic.Lint

/-!
# Basic linter types and attributes

This file defines the basic types and attributes used by the linting
framework.  A linter essentially consists of a function
`(declaration : Name) → MetaM (Option MessageData)`, this function together with some
metadata is stored in the `Linter` structure. We define two attributes:

 * `@[env_linter]` applies to a declaration of type `Linter`
   and adds it to the default linter set.

 * `@[nolint linterName]` omits the tagged declaration from being checked by
   the linter with name `linterName`.
-/

/--
Returns true if `decl` is an automatically generated declaration.

Also returns true if `decl` is an internal name or created during macro
expansion.
-/
def isAutoDecl (decl : Name) : CoreM Bool := do
  if decl.hasMacroScopes then return true
  if decl.isInternal then return true
  let env ← getEnv
  if isReservedName env decl then return true
  if let Name.str n s := decl then
    if (← isAutoDecl n) then return true
    if s.startsWith "proof_" || s.startsWith "match_" || s.startsWith "unsafe_" then return true
    if env.isConstructor n && s ∈ ["injEq", "inj", "sizeOf_spec", "elim", "noConfusion"] then
      return true
    if let ConstantInfo.inductInfo _ := (← getEnv).find? n then
      if s.startsWith "brecOn_" || s.startsWith "below_" then return true
      if s ∈ [casesOnSuffix, recOnSuffix, brecOnSuffix, belowSuffix,
          "ndrec", "ndrecOn", "noConfusionType", "noConfusion", "ofNat", "toCtorIdx", "ctorIdx",
          "ctorElim", "ctorElimType"] then
        return true
      if let some _ := isSubobjectField? env n (.mkSimple s) then
        return true
  pure false

/-- A linting test for the `#lint` command. -/
structure Linter where
  /-- `test` defines a test to perform on every declaration. It should never fail. Returning `none`
  signifies a passing test. Returning `some msg` reports a failing test with error `msg`. -/
  test : Name → MetaM (Option MessageData)
  /-- `noErrorsFound` is the message printed when all tests are negative -/
  noErrorsFound : MessageData
  /-- `errorsFound` is printed when at least one test is positive -/
  errorsFound : MessageData
  /-- If `isFast` is false, this test will be omitted from `#lint-`. -/
  isFast := true

/-- A `NamedLinter` is a linter associated to a particular declaration. -/
structure NamedLinter extends Linter where
  /-- The name of the named linter. This is just the declaration name without the namespace. -/
  name : Name
  /-- The linter declaration name -/
  declName : Name

/-- Gets a linter by declaration name. -/
def getLinter (name declName : Name) : CoreM NamedLinter := unsafe
  return { ← evalConstCheck Linter ``Linter declName with name, declName }

/-- Defines the `env_linter` extension for adding a linter to the default set. -/
initialize batteriesLinterExt :
    PersistentEnvExtension (Name × Bool) (Name × Bool) (NameMap (Name × Bool)) ←
  let addEntryFn := fun m (n, b) => m.insert (n.updatePrefix .anonymous) (n, b)
  registerPersistentEnvExtension {
    mkInitial := pure {}
    addImportedFn := fun nss => pure <|
      nss.foldl (init := {}) fun m ns => ns.foldl (init := m) addEntryFn
    addEntryFn
    exportEntriesFn := fun es => es.foldl (fun a _ e => a.push e) #[]
  }

/--
Defines the `@[env_linter]` attribute for adding a linter to the default set.
The form `@[env_linter disabled]` will not add the linter to the default set,
but it will be shown by `#list_linters` and can be selected by the `#lint` command.

Linters are named using their declaration names, without the namespace. These must be distinct.
-/
syntax (name := env_linter) "env_linter" &" disabled"? : attr

initialize registerBuiltinAttribute {
  name := `env_linter
  descr := "Use this declaration as a linting test in #lint"
  add   := fun decl stx kind => do
    let dflt := stx[1].isNone
    unless kind == .global do throwError "invalid attribute `env_linter`, must be global"
    let shortName := decl.updatePrefix .anonymous
    if let some (declName, _) := (batteriesLinterExt.getState (← getEnv)).find? shortName then
      Elab.addConstInfo stx declName
      throwError
        "invalid attribute `env_linter`, linter `{shortName}` has already been declared"
    /- Just as `env_linter`s must be `global`, they also must be accessible from `#lint`, and thus
    must be `public` and `meta`.

    `Linter.mk` is already `meta` and thus will likely cause an error anyway, but the explicit
    instruction to mark this declaration `meta` might help the user resolve that and similar
    errors. -/
    let isPublic := !isPrivateName decl; let isMeta := isMarkedMeta (← getEnv) decl
    unless isPublic && isMeta do
      let mut modifiers := []
      unless isMeta   do modifiers := "meta"   :: modifiers
      unless isPublic do modifiers := "public" :: modifiers
      throwError "invalid attribute `env_linter`, \
        declaration `{.ofConstName decl}` must be marked `{" ".intercalate modifiers}`"
    let constInfo ← getConstInfo decl
    unless ← (isDefEq constInfo.type (mkConst ``Linter)).run' do
      throwError "`{.ofConstName decl}` must have type `{.ofConstName ``Linter}`, got \
        `{constInfo.type}`"
    modifyEnv fun env => batteriesLinterExt.addEntry env (decl, dflt)
}

/-- `@[nolint linterName]` omits the tagged declaration from being checked by
the linter with name `linterName`. -/
syntax (name := nolint) "nolint" (ppSpace ident)+ : attr

/-- Defines the user attribute `nolint` for skipping `#lint` -/
initialize nolintAttr : ParametricAttribute (Array Name) ←
  registerParametricAttribute {
    name := `nolint
    descr := "Do not report this declaration in any of the tests of `#lint`"
    getParam := fun _ => fun
      | `(attr| nolint $[$ids]*) => ids.mapM fun id => withRef id <| do
        let shortName := id.getId.eraseMacroScopes
        let some (declName, _) := (batteriesLinterExt.getState (← getEnv)).find? shortName
          | throwError "linter '{shortName}' not found"
        Elab.addConstInfo id declName
        pure shortName
      | _ => Elab.throwUnsupportedSyntax
  }

/-- Returns true if `decl` should be checked
using `linter`, i.e., if there is no `nolint` attribute. -/
def shouldBeLinted [Monad m] [MonadEnv m] (linter : Name) (decl : Name) : m Bool :=
  return !((nolintAttr.getParam? (← getEnv) decl).getD #[]).contains linter

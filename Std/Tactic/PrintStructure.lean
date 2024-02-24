/-
Copyright (c) 2024 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: François G. Dorais
-/
import Lean.Elab

open Lean Elab Command

/--
The command `#print structure foo` will print information about the structure `foo`.
-/
syntax (name := printStructure) "#print" "structure" (&"flat" <|> &"full")? ident : command

/-- Configuration options for print structure -/
structure PrintStructureConfig where
  /-- Also print fields from subobjects -/
  flat : Bool := false
  /-- Include subobject projections -/
  includeSubobjectFields : Bool := true

private def flatConfig : PrintStructureConfig where
  flat := true
  includeSubobjectFields := false

private def fullConfig : PrintStructureConfig where
  flat := true
  includeSubobjectFields := true

private def printStructureMsg (structName : Name) (cfg : PrintStructureConfig := {}) :
    MetaM String := do
  let env ← getEnv
  if isStructure env structName then
    let indInfo ← getConstInfoInduct structName
    let [ctorName] := indInfo.ctors | failure
    let ctorInfo ← getConstInfoCtor ctorName
    let levels := if indInfo.levelParams = [] then "" else
      ".{" ++ ", ".intercalate (indInfo.levelParams.map Name.toString) ++ "}"
    let mut msg :=
      s!"structure {structName}{levels} : {← Meta.ppExpr indInfo.type}\n\
        constructor:\n\
        {ctorName} : {← Meta.ppExpr ctorInfo.type}\n\
        fields:\n"
    let fieldNames :=
      if cfg.flat then
        getStructureFieldsFlattened env structName cfg.includeSubobjectFields
      else
        getStructureFields env structName
    for fieldName in fieldNames do
      if let some structName := findField? env structName fieldName then
        let projInfo ← getConstInfo (structName ++ fieldName)
        msg := msg ++ s!"{fieldName} : {← Meta.ppExpr projInfo.type}\n"
    return msg
  else
    throwError "expected structure"

/--
Implementation for `#print structure` command
-/
@[command_elab printStructure] def elabPrintStructure : CommandElab
  | `(#print%$tk structure $id:ident) =>
    liftTermElabM do
      if let [name] ← resolveGlobalConst id then
        let msg ← printStructureMsg name
        logInfoAt tk msg
  | `(#print%$tk structure flat $id:ident) =>
    liftTermElabM do
      if let [name] ← resolveGlobalConst id then
        let msg ← printStructureMsg name flatConfig
        logInfoAt tk msg
  | `(#print%$tk structure full $id:ident) =>
    liftTermElabM do
      if let [name] ← resolveGlobalConst id then
        let msg ← printStructureMsg name fullConfig
        logInfoAt tk msg
  | _ => throwUnsupportedSyntax

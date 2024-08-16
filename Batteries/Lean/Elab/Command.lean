/-
Copyright (c) 2023 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Lean.Elab.Command

/-!
# Command elaboration helpers
-/

namespace Lean.Elab.Command

/--
If the option `optName` exists, set it to `val`.
Will still fail if the set value does not match the option's proper type
(e.g., setting a string value to a boolean option).

Thus, ``trySetOption `myOttr  true`` is essentially equivalent to
the command `set_option myOpt true`, except it will not error if the
option name does not exist.
-/
def trySetOption (optName : Name) (val : DataValue) : CommandElabM PUnit := do
  let some decl := (← getOptionDecls).find? optName | return
  unless decl.defValue.sameCtor val do
    throwError "type mismatch for '{optName}'"
  modifyScope (fun s => {s with opts := s.opts.insert optName val})

/--
For each named option which exists, set its value.
Will still fail if the set value does not match the option's proper type
(e.g., setting a string value to a boolean option).
-/
def trySetOptions (settings : Array (Name × DataValue)) : CommandElabM PUnit := do
  let opts ← getOptions
  let decls ← getOptionDecls
  let opts ← settings.foldlM (init := opts) fun opts (optName, val) => do
    let some decl := decls.find? optName | return opts
    unless decl.defValue.sameCtor val do
      throwError "type mismatch for '{optName}'"
    return opts.insert optName val
  modifyScope ({· with opts})

/--
If `attrName` exists, try to erase it from the specified declaration names,
skipping any that do not exist (or, due to implementation constraints,
fail to erase).

Thus, ``tryEraseAttr `my_attr  #[`foo, `bar]`` is essentially equivalent to
the command `attribute [-my_attr] foo bar`, except it will not error if the
attribute or declaration names do not exist.
-/
def tryEraseAttr (attrName : Name) (declNames : Array Name) : CoreM PUnit := do
  let attrState := attributeExtension.getState (← getEnv)
  let some attr := attrState.map.find? attrName | return
  declNames.forM fun declName =>
    try
      attr.erase declName
    catch _ =>
      -- This consumes all types of errors, rather than just existence ones,
      -- but there does not appear to be a better general way to achieve this.
      pure ()

/--
for each named attribute which exists,
erase from it the specified declaration names, ignoring failures.
-/
def tryEraseAttrs (attrs :  Array (Name × Array Name)) : CommandElabM PUnit := do
  liftCoreM <| attrs.forM fun ⟨attrName, declNames⟩ => tryEraseAttr attrName declNames

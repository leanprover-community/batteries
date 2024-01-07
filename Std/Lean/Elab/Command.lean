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
For each named option which exists, set its value.
Will still fail if the set value does not match the option's proper type
(e.g., setting a string value to a boolean option).
-/
def trySetOptions (settings : Array (Name × DataValue)) : CommandElabM PUnit := do
  let opts ← getOptions
  let ⟨_, opts⟩ ← StateT.run (s := opts) <| settings.forM fun ⟨optName, val⟩ => do
    if let .ok decl ← getOptionDecl optName |>.toBaseIO then
      unless decl.defValue.sameCtor val do
        throwError "type mismatch for '{optName}'"
      modify (·.insert optName val)
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
  if let some attr := attrState.map.find? attrName then
    declNames.forM fun declName =>
      try
        attr.erase declName
      catch _ =>
        -- This consumes all types of errors, rather than just existence ones,
        -- but there does not appear to be a better general way to achieve this
        pure ()

/--
for each named attribute which exists,
erase from it the specified declaration names, ignoring failures.
-/
def tryEraseAttrs (attrs :  Array (Name × Array Name)) : CommandElabM PUnit := do
  liftCoreM <| attrs.forM fun ⟨attrName, declNames⟩ => tryEraseAttr attrName declNames

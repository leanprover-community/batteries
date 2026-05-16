/-
Copyright (c) 2025 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa, François G. Dorais
-/
module

public meta import Lean.Elab.Command
public meta import Lean.Linter
public meta import Std.Time.Format
public import Std.Time.Date

/-!
# The `deprecated.module` linter

This linter emits a warning when a deprecated imported. Reasons for module
deprecation include renaming, splitting, obsolescence.

The usage is as follows:
```lean
import A
import B
import C
...

deprecated_module "Optional string with further details" (since := "yyyy-mm-dd")
```
in module `X` with the expectation that `X` contains nothing else.

This triggers the `deprecated.module` linter to notify every file with
`import X` to instead import the *direct imports* of `X`, that is modules
`A`, `B`, `C`,...

The deprecated module linter is enabled by default. To disable it set option
`linter.deprecated.module` to `false`.

Some projects (like Mathlib) are designed so that the root module imports
everything, regardless of deprecation status. In such cases, there is an
additional linter option `linter.deprecated.module.exclude_root` that
prevents the deprecated module linter on the root module when set to `true`.
This option has no effect if the deprecated module linter is disabled.
-/

meta section

open Lean Elab Command Linter

namespace Batteries.Linter

/--
The deprecated module linter emits a warning when a module that has been
deprecated is imported. This linter is enabled by default, since this linter
is designed to warn downstream projects of changes in their dependencies.
-/
public register_option linter.deprecated.module : Bool := {
  defValue := true
  descr := "enable the `deprecated.module` linter"
}

/--
The option `deprecated.module.exclude_root` controls whether the `deprecated.module` linter will
run on root modules. The default value is `false`; this option has no effect if the
`deprecated.module` linter is disabled.

Some root modules (e.g. `Mathlib`) are designed to import every module regardless of deprecation
status. This option allows to exclude deprecated import checking in such cases.
-/
public register_option linter.deprecated.module.exclude_root : Bool := {
  defValue := false
  descr := "disable the `deprecated.module` linter on project root"
}

/--
The deprecated module extension is a `HashMap` where keys are module names and
values are pairs consisting of:
* an array of `Name`s of modules that should be imported instead,
* an optional `String` containing further messages to be displayed with the
  deprecation to the environment.
-/
public initialize deprecatedModuleExt :
    SimplePersistentEnvExtension
      (Name × Array Name × Option String) (Std.HashMap Name (Array Name × Option String)) ←
  registerSimplePersistentEnvExtension {
    addImportedFn := (·.foldl Std.HashMap.insertMany {})
    addEntryFn := (Function.uncurry ·.insert)
  }

/-- Check whether a module is deprecated. -/
@[inline]
def isDeprecatedModule (env : Environment) (modName : Name) : Bool :=
  deprecatedModuleExt.getState env |>.contains modName

/--
`addModuleDeprecation` adds the current module to the deprecated module
extension. The value consists of the module's direct imports excluding two:
* The `Init` module since it is always imported.
* The `Batteries.Linter.DeprecatedModule` which is imported to access the
  deprecated module command.
-/
def addModuleDeprecation {m : Type → Type} [Monad m] [MonadEnv m] (msg? : Option String) :
    m Unit := do
  let modName ← getMainModule
  let replNames := (← getEnv).imports |>.filterMap fun i =>
    if i.module == `Init || i.module == `Batteries.Linter.DeprecatedModule then
      none
    else
      some i.module
  modifyEnv (deprecatedModuleExt.addEntry · (modName, replNames, msg?))

/--
`deprecated_module "Optional string" (since := "yyyy-mm-dd")` deprecates the
current module `A` in favor of its direct imports. This means that any file
that directly imports `A` will get a notification on the `import A` line
suggesting to instead import the *direct imports* of `A`.
-/
elab (name := deprecatedModule) "deprecated_module " msg?:(str ppSpace)?
    "(" &"since " ":= " when:str ")" : command => do
  if let .error _parsedDate := Std.Time.PlainDate.fromLeanDateString when.getString then
    throwError "Invalid date: the expected format is \"yyyy-mm-dd\""
  addModuleDeprecation <| msg?.map (·.getString)
  -- Disable the linter, so that it does not complain in the file with the deprecation.
  elabCommand <| mkNullNode #[← `(set_option linter.deprecated.module false)]

/--
A utility command to show the current entries of the `deprecatedModuleExt` in the format:
```
Deprecated modules

'BatteriesTest.DeprecatedModule' deprecates to
#[Batteries.Tactic.Alias, Batteries.Tactic.Basic]
with message 'We can also give more details about the deprecation'
```
-/
elab "#show_deprecated_modules" : command => do
  let deprecated := deprecatedModuleExt.getState (← getEnv)
  logInfo <| "\n".intercalate <|
    deprecated.fold (init := ["Deprecated modules\n"]) fun nms i (deps, msg?) =>
      let msg := match msg? with | some str => s!"message '{str}'" | none => "no message"
      nms ++ [s!"'{i}' deprecates to\n{deps}\nwith {msg}\n"]

/--
`IsLaterCommand` is an `IO.Ref` that starts out being `false`.
As soon as a (non-import) command in a file is processed, the `deprecated.module` linter
sets it to `true`.
If it is `false`, then the `deprecated.module` linter will check for deprecated modules.

This is used to ensure that the linter performs the deprecation checks only once per file.
There are possible concurrency issues, but they should not be particularly worrying:
* the linter check should be relatively quick;
* the only way in which the linter could change what it reports is if the imports are changed
  and a change in imports triggers a rebuild of the whole file anyway, resetting the `IO.Ref`.
-/
initialize IsLaterCommand : IO.Ref Bool ← IO.mkRef false

-- Note: from Mathlib.Tactic.Linter.Header
partial def getImportIds (s : Syntax) : Array Syntax :=
  let rest : Array Syntax := (s.getArgs.map getImportIds).flatten
  -- Check if this is an import node by kind, rather than pattern matching all optional modifiers.
  -- This is more robust if the import syntax changes.
  if s.isOfKind `Lean.Parser.Module.import then
    -- The module name is the last identifier in the import node arguments
    match s.getArgs.filter (·.isIdent) |>.back? with
    | some n => rest.push n
    | none => rest
  else
    rest

@[inherit_doc Batteries.Linter.linter.deprecated.module]
def deprecatedModuleLinter : Linter where run := withSetOptionIn fun stx => do
  unless getLinterValue linter.deprecated.module (← getLinterOptions) do
    return
  if (← get).messages.hasErrors then
    return
  -- Exclude root module?
  if getLinterValue linter.deprecated.module.exclude_root (← getLinterOptions)
      && (← getMainModule).getNumParts == 1 then
    return
  let laterCommand ← IsLaterCommand.get
  -- If `laterCommand` is `true`, then the linter already did what it was supposed to do.
  -- If `laterCommand` is `false` at the end of file, the file is an import-only file and
  -- the linter should not do anything.
  if laterCommand || (Parser.isTerminalCommand stx && !laterCommand) then
    return
  IsLaterCommand.set true
  let deprecations := deprecatedModuleExt.getState (← getEnv)
  if deprecations.isEmpty then
    return
  if stx.isOfKind ``deprecatedModule then return
  let fm ← getFileMap
  let (importStx, _) ←
    Parser.parseHeader { inputString := fm.source, fileName := ← getFileName, fileMap := fm }
  let modulesWithNames := (getImportIds importStx).map fun i => (i, i.getId)
  for (i, preferred, msg?) in deprecations do
    for (nmStx, _) in modulesWithNames.filter (·.2 == i) do
      Linter.logLint linter.deprecated.module nmStx
        m!"{msg?.getD ""}\n\
          '{nmStx}' has been deprecated: please replace this import by\n\n\
          {String.join (preferred.foldl (·.push s!"import {·}\n") #[]).toList}"

initialize addLinter deprecatedModuleLinter

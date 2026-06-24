/-
Copyright (c) 2020 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Robert Y. Lewis, Gabriel Ebner
-/
module

public meta import Lean.Elab.Command
public meta import Batteries.Linter.Basic

public meta section

/-!
# Linter frontend and commands

This file defines the linter commands which spot common mistakes in the code.
* `#lint`: check all declarations in the current file
* `#lint in Pkg`: check all declarations in the package `Pkg`
  (so excluding core or other projects, and also excluding the current file)
* `#lint in all`: check all declarations in the environment
  (the current file and all imported files)

For a list of default / non-default linters, see the "Linting Commands" user command doc entry.

The command `#list_linters` prints a list of the names of all available linters.

You can append a `*` to any command (e.g. `#lint* in Batteries`) to omit the slow tests.

You can append a `-` to any command (e.g. `#lint- in Batteries`) to run a silent lint
that suppresses the output if all checks pass.
A silent lint will fail if any test fails.

You can append a `+` to any command (e.g. `#lint+ in Batteries`) to run a verbose lint
that reports the result of each linter, including  the successes.

You can append a sequence of linter names to any command to run extra tests, in addition to the
default ones. e.g. `#lint doc_blame_thm` will run all default tests and `doc_blame_thm`.

You can append `only name1 name2 ...` to any command to run a subset of linters, e.g.
`#lint only unused_arguments in Batteries`

You can add custom linters by defining a term of type `Linter` with the
`@[env_linter]` attribute.
A linter defined with the name `Batteries.Linter.myNewCheck` can be run with `#lint myNewCheck`
or `#lint only myNewCheck`.
If you add the attribute `@[env_linter disabled]` to `linter.myNewCheck` it will be
registered, but not run by default.

Adding the attribute `@[nolint doc_blame unused_arguments]` to a declaration
omits it from only the specified linter checks.

## Tags

sanity check, lint, cleanup, command, tactic
-/

namespace Batteries.Linter
open Lean Elab Command Tactic

/-- Verbosity for the linter output. -/
inductive LintVerbosity
  /-- `low`: only print failing checks, print nothing on success. -/
  | low
  /-- `medium`: only print failing checks, print confirmation on success. -/
  | medium
  /-- `high`: print output of every check. -/
  | high
  deriving Inhabited, DecidableEq, Repr

/-- `getChecks slow runOnly runAlways` produces a list of linters.
`runOnly` is an optional list of names that should resolve to declarations with type `NamedLinter`.
If populated, only these linters are run (regardless of the default configuration).
`runAlways` is an optional list of names that should resolve to declarations with type
`NamedLinter`. If populated, these linters are always run (regardless of their configuration).
Specifying a linter in `runAlways` but not `runOnly` is an error.
Otherwise, it uses all enabled linters in the environment tagged with `@[env_linter]`.
If `slow` is false, it only uses the fast default tests. -/
def getChecks (slow : Bool) (runOnly : Option (List Name)) (runAlways : Option (List Name)) :
    CoreM (Array NamedLinter) := do
  let mut result := #[]
  for (name, declName, default) in batteriesLinterExt.getState (← getEnv) do
    let shouldRun := match (runOnly, runAlways) with
      | (some only, some always) => only.contains name && (always.contains name || default)
      | (some only, none) => only.contains name
      | (none, some always) => default || always.contains name
      | _ => default
    if shouldRun then
      let linter ← getLinter name declName
      if slow || linter.isFast then
        let _ := Inhabited.mk linter
        result := result.binInsert (·.name.lt ·.name) linter
  pure result

/-- Traces via `IO.println` if `inIO` is `true`, and via `trace[...]` otherwise. It seems that
`trace` messages in a running `CoreM` are not propagated through to `IO` in the current setup. We
use `IO.println` directly instead of running `printTraces` at the end of our `CoreM` action so that
trace messages are printed to stdout immediately, and are not lost if any part of the action hangs.

This declaration is `macro_inline`, so it should have the same thunky behavior as `trace[...]`. -/
@[macro_inline, expose]
def traceLintCore (msg : String) (inIO : Bool) : CoreM Unit := do
  if inIO then
    if ← getBoolOption `trace.Batteries.Lint then
      IO.println msg
  else
    trace[Batteries.Lint] msg

/-- Traces via `IO.println` if `inIO` is `true`, and via `trace[...]` otherwise. Prepends
`currentModule` and `linter` (if present).

This declaration is `macro_inline`, so it should have the same thunky behavior as `trace[...]`. -/
@[macro_inline, expose]
def traceLint (msg : String) (inIO : Bool) (currentModule linterName : Option Name := none) :
    CoreM Unit :=
  traceLintCore (inIO := inIO)
    s!"{if let some m := currentModule then s!"[{m}] " else ""}\
      {if let some l := linterName then s!"- {l}: " else ""}\
      {msg}"

/--
Runs all the specified linters on all the specified declarations in parallel,
producing a list of results.
-/
def lintCore (decls : Array Name) (linters : Array NamedLinter)
    -- For tracing:
    (currentModule : Option Name := none) (inIO : Bool := false) :
    CoreM (Array (NamedLinter × Std.HashMap Name MessageData)) := do
  traceLint
      s!"Running linters:\n  {"\n  ".intercalate <| linters.map (s!"{·.name}") |>.toList}"
      inIO currentModule

  let tasks : Array (NamedLinter × Array (Name × Task (Except Exception <| Option MessageData))) ←
    linters.mapM fun linter => do
      traceLint "(0/2) Starting..." inIO currentModule linter.name
      let decls ← decls.filterM (shouldBeLinted linter.name)
      (linter, ·) <$> decls.mapM fun decl => (decl, ·) <$> do
        let act : MetaM (Option MessageData) := do
          let result ← linter.test decl
          if inIO then
            -- Ensure any trace messages are propagated to stdout
            printTraces
          return result
        EIO.asTask <| (← Core.wrapAsync (fun _ =>
          act |>.run' mkMetaContext -- We use the context used by `Command.liftTermElabM`
        ) (cancelTk? := none)) ()

  let result ← tasks.mapM fun (linter, decls) => do
    traceLint "(1/2) Getting..." inIO currentModule linter.name
    let mut msgs : Std.HashMap Name MessageData := {}
    for (declName, msgTask) in decls do
      let msg? ← match msgTask.get with
      | Except.ok msg? => pure msg?
      | Except.error err => pure m!"LINTER FAILED:\n{err.toMessageData}"

      if let .some msg := msg? then
        msgs := msgs.insert declName msg
    traceLint
      s!"(2/2) {if msgs.isEmpty then "Passed!" else
        s!"Failed with {msgs.size} messages\
        {if inIO then ", but these may include declarations in `nolints.json`" else ""}."}"
      inIO currentModule linter.name
    pure (linter, msgs)
  traceLint "Completed linting!" inIO currentModule
  return result


/-- Sorts a map with declaration keys as names by line number. -/
def sortResults (results : Std.HashMap Name α) : CoreM <| Array (Name × α) := do
  let mut key : Std.HashMap Name Nat := {}
  for (n, _) in results.toArray do
    if let some range ← findDeclarationRanges? n then
      key := key.insert n <| range.range.pos.line
  pure $ results.toArray.qsort fun (a, _) (b, _) => key.getD a 0 < key.getD b 0

/-- Formats a linter warning as `#check` command with comment. -/
def printWarning (declName : Name) (warning : MessageData) (useErrorFormat : Bool := false)
  (filePath : System.FilePath := default) : CoreM MessageData := do
  if useErrorFormat then
    if let some range ← findDeclarationRanges? declName then
      let msg ← addMessageContextPartial
        m!"{filePath}:{range.range.pos.line}:{range.range.pos.column + 1}: error: {
          ← mkConstWithLevelParams declName} {warning}"
      return msg
  addMessageContextPartial m!"#check {← mkConstWithLevelParams declName} /- {warning} -/"

/-- Formats a map of linter warnings using `print_warning`, sorted by line number. -/
def printWarnings (results : Std.HashMap Name MessageData) (filePath : System.FilePath := default)
    (useErrorFormat : Bool := false) : CoreM MessageData := do
  (MessageData.joinSep ·.toList Format.line) <$>
    (← sortResults results).mapM fun (declName, warning) =>
      printWarning declName warning (useErrorFormat := useErrorFormat) (filePath := filePath)

/--
Formats a map of linter warnings grouped by filename with `-- filename` comments.
The first `drop_fn_chars` characters are stripped from the filename.
-/
def groupedByFilename (results : Std.HashMap Name MessageData) (useErrorFormat : Bool := false) :
    CoreM MessageData := do
  let sp ← if useErrorFormat then getSrcSearchPath else pure {}
  let grouped : Std.HashMap Name (System.FilePath × Std.HashMap Name MessageData) ←
    results.foldM (init := {}) fun grouped declName msg => do
      let mod ← findModuleOf? declName
      let mod := mod.getD (← getEnv).mainModule
      grouped.insert mod <$>
        match grouped[mod]? with
        | some (fp, msgs) => pure (fp, msgs.insert declName msg)
        | none => do
          let fp ← if useErrorFormat then
            pure <| (← sp.findWithExt "lean" mod).getD (modToFilePath "." mod "lean")
          else pure default
          pure (fp, .insert {} declName msg)
  let grouped' := grouped.toArray.qsort fun (a, _) (b, _) => toString a < toString b
  (MessageData.joinSep · (Format.line ++ Format.line)) <$>
    grouped'.toList.mapM fun (mod, fp, msgs) => do
      pure m!"-- {mod}\n{← printWarnings msgs (filePath := fp) (useErrorFormat := useErrorFormat)}"

/--
Formats the linter results as Lean code with comments and `#check` commands.
-/
def formatLinterResults
    (results : Array (NamedLinter × Std.HashMap Name MessageData))
    (decls : Array Name)
    (groupByFilename : Bool)
    (whereDesc : String) (runSlowLinters : Bool)
    (verbose : LintVerbosity) (numLinters : Nat) (useErrorFormat : Bool := false) :
    CoreM MessageData := do
  let formattedResults ← results.filterMapM fun (linter, results) => do
    if !results.isEmpty then
      let warnings ←
        if groupByFilename || useErrorFormat then
          groupedByFilename results (useErrorFormat := useErrorFormat)
        else
          printWarnings results
      pure $ some m!"/- The `{linter.name}` linter reports:\n{linter.errorsFound
        }\nThis linter can be disabled with `@[nolint {linter.name}]`. -/\n{warnings}\n"
    else if verbose = LintVerbosity.high then
      pure $ some m!"/- OK: {linter.noErrorsFound} -/"
    else
      pure none
  let mut s := MessageData.joinSep formattedResults.toList Format.line
  let numAutoDecls := (← decls.filterM isAutoDecl).size
  let failed := results.map (·.2.size) |>.foldl (·+·) 0
  unless verbose matches LintVerbosity.low do
    s := m!"-- Found {failed} error{if failed == 1 then "" else "s"
      } in {decls.size - numAutoDecls} declarations (plus {
      numAutoDecls} automatically generated ones) {whereDesc
      } with {numLinters} linters\n\n{s}"
  unless runSlowLinters do s := m!"{s}-- (slow linters skipped)\n"
  pure s

/-- Get the list of declarations in the current module. -/
def getDeclsInCurrModule : CoreM (Array Name) := do
  pure $ (← getEnv).constants.map₂.foldl (init := #[]) fun r k _ => r.push k

/-- Get the list of all declarations in the environment. -/
def getAllDecls : CoreM (Array Name) := do
  pure $ (← getEnv).constants.map₁.fold (init := ← getDeclsInCurrModule) fun r k _ => r.push k

/-- Get the list of all declarations in the specified package. -/
def getDeclsInPackage (pkg : Name) : CoreM (Array Name) := do
  let env ← getEnv
  let mut decls ← getDeclsInCurrModule
  let modules := env.header.moduleNames.map (pkg.isPrefixOf ·)
  return env.constants.map₁.fold (init := decls) fun decls declName _ =>
    if modules[env.const2ModIdx[declName]?.get!]! then
      decls.push declName
    else decls

/-- The `in foo` config argument allows running the linter on a specified project. -/
syntax inProject := " in " ident

open Elab Command in
/-- The command `#lint` runs the linters on the current file (by default).

`#lint only someLinter` can be used to run only a single linter. -/
elab tk:"#lint" verbosity:("+" <|> "-")? fast:"*"? only:(&" only")?
    linters:(ppSpace ident)* project:(inProject)? : command => do
  let (decls, whereDesc, groupByFilename) ← match project with
    | none => do pure (← liftCoreM getDeclsInCurrModule, "in the current file", false)
    | some cfg => match cfg with
      | `(inProject| in $id) =>
        let id := id.getId.eraseMacroScopes
        if id == `all then
          pure (← liftCoreM getAllDecls, "in all files", true)
        else
          pure (← liftCoreM (getDeclsInPackage id), s!"in {id}", true)
      | _ => throwUnsupportedSyntax
  let verbosity : LintVerbosity ← match verbosity with
    | none => pure .medium
    | some ⟨.node _ `token.«+» _⟩ => pure .high
    | some ⟨.node _ `token.«-» _⟩ => pure .low
    | _ => throwUnsupportedSyntax
  let fast := fast.isSome
  let onlyNames : Option (List Name) := match only.isSome with
    | true => some (linters.map fun l => l.getId).toList
    | false => none
  let linters ← liftCoreM do
    let mut result ← getChecks (slow := !fast) (runOnly := onlyNames) none
    let linterState := batteriesLinterExt.getState (← getEnv)
    for id in linters do
      let name := id.getId.eraseMacroScopes
      let some (declName, _) := linterState.find? name | throwErrorAt id "not a linter: {name}"
      Elab.addConstInfo id declName
      let linter ← getLinter name declName
      result := result.binInsert (·.name.lt ·.name) linter
    pure result
  let results ← liftCoreM <| lintCore decls linters
  let failed := results.any (!·.2.isEmpty)
  let mut fmtResults ← liftCoreM <|
    formatLinterResults results decls (groupByFilename := groupByFilename)
      whereDesc (runSlowLinters := !fast) verbosity linters.size
  if failed then
    logError fmtResults
  else if verbosity != LintVerbosity.low then
    logInfoAt tk m!"{fmtResults}\n-- All linting checks passed!"

open Elab Command in
/-- The command `#list_linters` prints a list of all available linters. -/
elab "#list_linters" : command => do
  let mut result := #[]
  for (name, _, dflt) in batteriesLinterExt.getState (← getEnv) do
    result := result.binInsert (·.1.lt ·.1) (name, dflt)
  let mut msg := m!"Available linters (linters marked with (*) are in the default lint set):"
  for (name, dflt) in result do
    msg := msg ++ m!"\n{name}{if dflt then " (*)" else ""}"
  logInfo msg

initialize registerTraceClass `Batteries.Lint

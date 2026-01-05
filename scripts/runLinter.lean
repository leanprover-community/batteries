import Batteries.Tactic.Lint
import Batteries.Data.Array.Basic
import Lake.CLI.Main

open Lean Core Elab Command Batteries.Tactic.Lint
open System (FilePath)

/-- The list of `nolints` pulled from the `nolints.json` file -/
abbrev NoLints := Array (Name × Name)

/-- Read the given file path and deserialize it as JSON. -/
def readJsonFile (α) [FromJson α] (path : System.FilePath) : IO α := do
  let _ : MonadExceptOf String IO := ⟨throw ∘ IO.userError, fun x _ => x⟩
  liftExcept <| fromJson? <|← liftExcept <| Json.parse <|← IO.FS.readFile path

/-- Serialize the given value `a : α` to the file as JSON. -/
def writeJsonFile [ToJson α] (path : System.FilePath) (a : α) : IO Unit :=
  IO.FS.writeFile path <| toJson a |>.pretty.push '\n'

open Lake

/-- Returns the root modules of `lean_exe` or `lean_lib` default targets in the Lake workspace. -/
def resolveDefaultRootModules : IO (Array Name) := do
  -- load the Lake workspace
  let (elanInstall?, leanInstall?, lakeInstall?) ← findInstall?
  let config ← MonadError.runEIO <| mkLoadConfig { elanInstall?, leanInstall?, lakeInstall? }
  let some workspace ← loadWorkspace config |>.toBaseIO
    | throw <| IO.userError "failed to load Lake workspace"

  -- build an array of all root modules of `lean_exe` and `lean_lib` default targets
  let defaultTargetModules := workspace.root.defaultTargets.flatMap fun target =>
    if let some lib := workspace.root.findLeanLib? target then
      lib.roots
    else if let some exe := workspace.root.findLeanExe? target then
      #[exe.config.root]
    else
      #[]
  return defaultTargetModules

/-- Arguments for `runLinter`. -/
structure LinterConfig where
  /-- Whether to update nolints. Default is `false`; set to `true` with `--update`. -/
  updateNoLints : Bool := false
  /-- Whether to throw an error if necessary oleans are not already present (as opposed to building
  them). Default is `false`; set to `true` with `--no-build`. -/
  noBuild : Bool := false
  /-- Whether to enable tracing. Default is `false`; set to `true` with `--trace` or `-v`. -/
  trace := false

@[always_inline, inline]
private def Except.consError (e : ε) : Except (List ε) α → Except (List ε) α
  | Except.error errs => Except.error <| e :: errs
  | Except.ok _       => Except.error [e]

/--
Parse args list for `runLinter` and return the config and specified module arguments. Default
config settings are determined by the default values for fields of `LinterConfig`.

Throws an exception if unable to parse the arguments.
Returns `none` for the specified module if no module is specified.-/
def parseLinterArgs (args : List String) :
    Except (List String) (LinterConfig × Option Name) :=
  go {} args
where
  /-- Traverses the list, handling the last element as a module and erroring if parsing fails. -/
  go (parsed : LinterConfig) : List String → Except (List String) (LinterConfig × Option Name)
    | arg :: args@(_ :: _) =>
      if let some parsed := parseArg parsed arg then
        go parsed args
      else
        go parsed args |>.consError s!"could not parse argument '{arg}'"
    | [last] =>
      -- Try to parse it as a config argument, then as a module specification
      if let some parsed := parseArg parsed last then
        Except.ok (parsed, none)
      else
        match last.toName with
        | .anonymous => Except.error [s!"could not convert module '{last}' to `Name`"]
        | mod => Except.ok (parsed, some mod)
    | [] => Except.ok (parsed, none) -- only reachable with no arguments
  /-- Parses a single config argument. -/
  parseArg (parsed : LinterConfig) : String → Option LinterConfig
    | "--update"   => some { parsed with updateNoLints := true }
    | "--no-build" => some { parsed with noBuild := true }
    | "--trace"
    | "-v"         => some { parsed with trace := true }
    | _ => none

/--
Return an array of the modules to lint.

If `specifiedModule` is not `none` return an array containing only `specifiedModule`.
Otherwise, resolve the default root modules from the Lake workspace. -/
def determineModulesToLint (specifiedModule : Option Name) : IO (Array Name) := do
  match specifiedModule with
  | some module =>
    println!"Running linter on specified module: {module}"
    return #[module]
  | none =>
    println!"Automatically detecting modules to lint"
    let defaultModules ← resolveDefaultRootModules
    println!"Default modules: {defaultModules}"
    return defaultModules

/-- Run the Batteries linter on a given module and update the linter if `update` is `true`. -/
unsafe def runLinterOnModule (cfg : LinterConfig) (module : Name) : IO Unit := do
  let { updateNoLints, noBuild, trace } := cfg
  initSearchPath (← findSysroot)
  let rec
    /-- Builds `module` if the filepath `olean` does not exist. Throws if olean is not found and
    `noBuild := true`. -/
    buildIfNeeded (module : Name) : IO Unit := do
      let olean ← findOLean module
      unless (← olean.pathExists) do
        if noBuild then
          IO.println s!"Could not find olean for module `{module}` at given path:\n  \
            {olean}"
          IO.Process.exit 1
        else
          if trace then
            IO.println s!"Could not find olean for module `{module}` at given path:\n  \
              {olean}\n\
              Building `{module}`."
          -- run `lake build +module` (and ignore result) if the file hasn't been built yet
          let child ← IO.Process.spawn {
            cmd := (← IO.getEnv "LAKE").getD "lake"
            args := #["build", s!"+{module}"]
            stdin := .null
          }
          _ ← child.wait
          -- No need to trace on completion, lake's "Build completed successfully" reaches stdout

  buildIfNeeded module
  -- If the linter is being run on a target that doesn't import `Batteries.Tactic.List`,
  -- the linters are ineffective. So we import it here.
  let lintModule := `Batteries.Tactic.Lint
  buildIfNeeded lintModule
  let nolintsFile : FilePath := "scripts/nolints.json"
  let nolints ← if ← nolintsFile.pathExists then
    readJsonFile NoLints nolintsFile
  else
    pure #[]
  unsafe Lean.enableInitializersExecution
  let env ← importModules #[module, lintModule] {} (trustLevel := 1024) (loadExts := true)
  let mut opts : Options := {}
  -- Propagate `trace` to `CoreM`
  if trace then
    opts := opts.setBool `trace.Batteries.Lint true
  let ctx := {
    fileName := ""
    fileMap := default
    options := opts  }
  let state := { env }
  Prod.fst <$> (CoreM.toIO · ctx state) do
    traceLint s!"Starting lint..." (inIO := true) (currentModule := module)
    let decls ← getDeclsInPackage module.getRoot
    let linters ← getChecks (slow := true) (runAlways := none) (runOnly := none)
    let results ← lintCore decls linters (inIO := true) (currentModule := module)
    if updateNoLints then
      traceLint s!"Updating nolints file at {nolintsFile}" (inIO := true) (currentModule := module)
      writeJsonFile (α := NoLints) nolintsFile <|
        .qsort (lt := fun (a, b) (c, d) => a.lt c || (a == c && b.lt d)) <|
        .flatten <| results.map fun (linter, decls) =>
        decls.fold (fun res decl _ => res.push (linter.name, decl)) #[]
    let results := results.map fun (linter, decls) =>
      .mk linter <| nolints.foldl (init := decls) fun decls (linter', decl') =>
        if linter.name == linter' then decls.erase decl' else decls
    let failed := results.any (!·.2.isEmpty)
    if failed then
      let fmtResults ←
        formatLinterResults results decls (groupByFilename := true) (useErrorFormat := true)
          s!"in {module}" (runSlowLinters := true) .medium linters.size
      IO.print (← fmtResults.toString)
      IO.Process.exit 1
    else
      IO.println s!"-- Linting passed for {module}."

/--
Usage: `runLinter [--update] [--trace | -v] [--no-build] [Batteries.Data.Nat.Basic]`

Runs the linters on all declarations in the given module
(or all root modules of Lake `lean_lib` and `lean_exe` default targets if no module is specified).

If `--update` is set, the `nolints` file is updated to remove any declarations that no longer need
to be nolinted.

If `--trace` (or, synonymously, `-v`) is set, tracing will be enabled and logged to stdout.

If `--no-build` is set, `runLinter` will throw if either the oleans to be linted or the oleans
which drive the linting itself are not present.
-/
unsafe def main (args : List String) : IO Unit := do
  let linterArgs := parseLinterArgs args
  let (cfg, mod?) ← match linterArgs with
    | Except.ok args => pure args
    | Except.error msgs => do
      IO.eprintln s!"Error parsing args:\n  {"\n  ".intercalate msgs}"
      IO.eprintln "Usage: \
        runLinter [--update] [--trace | -v] [--no-build] [Batteries.Data.Nat.Basic]"
      IO.Process.exit 1

  let modulesToLint ← determineModulesToLint mod?

  modulesToLint.forM <| runLinterOnModule cfg

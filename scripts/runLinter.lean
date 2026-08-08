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

/-- Return the lake workspace. -/
def getLakeWorkspace : IO Workspace := do
  -- load the Lake workspace
  let (elanInstall?, leanInstall?, lakeInstall?) ← findInstall?
  let config ← MonadError.runEIO <| mkLoadConfig { elanInstall?, leanInstall?, lakeInstall? }
  let some workspace ← loadWorkspace config |>.toBaseIO
    | throw <| IO.userError "failed to load Lake workspace"
  return workspace

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
Returns `none` for the specified module if no modules are specified.-/
def parseLinterArgs (args : List String) :
    Except (List String) (LinterConfig × List String) :=
  go {} [] args
where
  /-- Traverses the list, handling the non-flag elements as modules and erroring if parsing fails. -/
  go (parsed : LinterConfig) (specs: List String) : List String → Except (List String) (LinterConfig × List String)
    | arg :: rest =>
      if let some parsed := parseArg parsed arg then
        go parsed specs rest
      else
        go parsed (arg :: specs) rest
    | [] => Except.ok (parsed, specs.reverse)

  /-- Parses a single config argument. -/
  parseArg (parsed : LinterConfig) : String → Option LinterConfig
    | "--update"   => some { parsed with updateNoLints := true }
    | "--no-build" => some { parsed with noBuild := true }
    | "--trace"
    | "-v"         => some { parsed with trace := true }
    | _ => none

/-- Get the names of lean modules referenced by a `BuildKey`. -/
def getModulesOfKey (workspace : Workspace) : BuildKey → IO (Option (Array Name × (Name → Bool)))
    | .module modName
    | .packageModule _ modName => return some (#[modName], (· == modName))
    | .packageTarget _pkgName targetName => do
      if let some lib := workspace.findLeanLib? targetName then
        let mods ← lib.getModuleArray
        return some (mods.map (·.name), lib.isLocalModule)
      else if let some exe := workspace.findLeanExe? targetName then
        return some (#[exe.config.root], (· == exe.config.root))
      else
        return none
    | .package pkgName => do
      let some pkg := workspace.findPackageByName? pkgName | return none
      let mut modules := #[]
      for lib in pkg.leanLibs do
        let mods ← lib.getModuleArray
        modules := modules ++ mods.map (·.name)
      for exe in pkg.leanExes do
        modules := modules.push exe.config.root
      return some (modules, pkg.isLocalModule)
    | .facet target _ => getModulesOfKey workspace target

/--
Return an array of the lint groups (name and associated modules) to lint by parsing the workspace and target specs. -/
def determineModulesToLint (targetSpecs : List String) : IO (Array (String × Array Name × (Name → Bool))) := do
  let workspace ← getLakeWorkspace

  let specs ← match ← parseTargetSpecs workspace targetSpecs |>.toBaseIO with
    | .ok specs => pure specs
    | .error err => throw <| IO.userError (toString err)

  let mut groups := #[]
  for spec in specs do
    if let some modules ← getModulesOfKey workspace spec.info.key then
      groups := groups.push (toString spec.info, modules)

  if groups.isEmpty then
    throw <| IO.userError "no targets found to lint"

  return groups

/-- Run the Batteries linter on a given group of modules and update the linter if `update` is `true`. -/
unsafe def runLinterOnModule (cfg : LinterConfig) (groupName : String) (modules : Array Name) (isLocal : Name → Bool) : IO Unit := do
  let { updateNoLints, noBuild, trace } := cfg
  initSearchPath (← findSysroot)

  let rec
    /-- Builds target if necessary oleans are not already present. Throws if olean is not found and
    `noBuild := true`. -/
    buildIfNeeded (target : String) (modules : Array Name) : IO Unit := do
      let firstMissing? ← (do
        for module in modules do
          let olean ← findOLean module
          unless ← olean.pathExists do
            return some (module, olean)
        return none)
      if let some (module, olean) := firstMissing? then
        if noBuild then
          IO.eprintln s!"[{target}] Could not find olean for module `{module}` at given path:\n  {olean}"
          IO.Process.exit 1
        else
          if trace then
            IO.println s!"[{target}] Could not find olean for module `{module}` at given path:\n  \
                {olean}\n\
                [{target}] Building `{target}`."
          -- run `lake build target` (and ignore result) if the file hasn't been built yet
          let child ← IO.Process.spawn {
            cmd := (← IO.getEnv "LAKE").getD "lake"
            args := #["build", target]
            stdin := .null
          }
          _ ← child.wait
          return
          -- No need to trace on completion, lake's "Build completed successfully" reaches stdout

  buildIfNeeded groupName modules
  -- If the linter is being run on a target that doesn't import `Batteries.Tactic.List`,
  -- the linters are ineffective. So we import it here.
  let lintModule := `Batteries.Tactic.Lint
  buildIfNeeded s!"+{lintModule}" #[lintModule]
  let nolintsFile : FilePath := "scripts/nolints.json"
  let nolints ← if ← nolintsFile.pathExists then
    readJsonFile NoLints nolintsFile
  else
    pure #[]
  unsafe Lean.enableInitializersExecution
  let imports : Array Import := modules.map (· : Name → Import) |>.push lintModule
  let env ← importModules imports {} (trustLevel := 1024) (loadExts := true)
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
    traceLint s!"Starting lint..." (inIO := true)
    let decls ← getDeclsFilterModuleName isLocal
    let linters ← getChecks (slow := true) (runAlways := none) (runOnly := none)
    let results ← lintCore decls linters (inIO := true)
    if updateNoLints then
      traceLint s!"Updating nolints file at {nolintsFile}" (inIO := true)
      writeJsonFile (α := NoLints) nolintsFile <|
        .qsort (lt := fun (a, b) (c, d) => a.lt c || (a == c && b.lt d)) <|
        .flatten <| results.map fun (linter, decls) =>
        decls.fold (fun res decl _ => res.push (linter.name, decl)) #[]
    if trace then
      let mut nolintTally : Std.HashMap Name Nat := {}
      for (linter, _) in nolints do
        nolintTally := nolintTally.alter linter fun
          | none   => some 1
          | some n => some (n+1)
      let msgs := nolintTally.toList.map fun (linter, n) => s!"{linter}: {n}"
      IO.println s!"[{groupName}] {nolintsFile} summary (number of nolints per linter):\n  \
        {"\n  ".intercalate msgs}"
    let results := results.map fun (linter, decls) =>
      .mk linter <| nolints.foldl (init := decls) fun decls (linter', decl') =>
        if linter.name == linter' then decls.erase decl' else decls
    let failed := results.any (!·.2.isEmpty)
    if failed then
      let fmtResults ←
        formatLinterResults results decls (groupByFilename := true) (useErrorFormat := true)
          s!"in {groupName}" (runSlowLinters := true) .medium linters.size
      IO.print (← fmtResults.toString)
      IO.Process.exit 1
    else
      IO.println s!"-- Linting passed for {groupName}."

/--
Usage: `runLinter [--update] [--trace | -v] [--no-build] [Batteries.Data.Nat.Basic]...`

Runs the linters on all declarations in modules provided by the given lake target
(or the default targets if none are specified). Modules within a target are imported into a single
environment.

If `--update` is set, the `nolints` file is updated to remove any declarations that no longer need
to be nolinted.

If `--trace` (or, synonymously, `-v`) is set, tracing will be enabled and logged to stdout.

If `--no-build` is set, `runLinter` will throw if either the oleans to be linted or the oleans
which drive the linting itself are not present.
-/
unsafe def main (args : List String) : IO Unit := do
  let linterArgs := parseLinterArgs args
  let (cfg, mods) ← match linterArgs with
    | Except.ok args => pure args
    | Except.error msgs => do
      IO.eprintln s!"Error parsing args:\n  {"\n  ".intercalate msgs}"
      IO.eprintln "Usage: \
        runLinter [--update] [--trace | -v] [--no-build] [Batteries.Data.Nat.Basic]..."
      IO.Process.exit 1

  let groupsToLint ← determineModulesToLint mods

  groupsToLint.forM fun (name, modules, isLocal) =>
    runLinterOnModule cfg name modules isLocal
  -- TODO: Remove manual Process.exit
  -- We are doing this to shortcut around a race in Lean's IO finalizers that we have observed in Mathlib CI
  -- (https://leanprover.zulipchat.com/#narrow/channel/287929-mathlib4/topic/slow.20linting.20step.20CI.3F/with/568830914)
  IO.Process.exit 0

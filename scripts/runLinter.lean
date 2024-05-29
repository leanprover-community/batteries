import Batteries.Tactic.Lint
import Batteries.Data.Array.Basic
import Batteries.Lean.Util.Path
import Lake.CLI.Main

open Lean Core Elab Command Std.Tactic.Lint
open System (FilePath)

/-- The list of `nolints` pulled from the `nolints.json` file -/
abbrev NoLints := Array (Name × Name)

/-- Read the given file path and deserialize it as JSON. -/
def readJsonFile (α) [FromJson α] (path : System.FilePath) : IO α := do
  let _ : MonadExceptOf String IO := ⟨throw ∘ IO.userError, fun x _ => x⟩
  liftExcept <| fromJson? <|← liftExcept <| Json.parse <|← IO.FS.readFile path

/-- Serialize the given value `a : α` to the file as JSON. -/
def writeJsonFile [ToJson α] (path : System.FilePath) (a : α) : IO Unit :=
  IO.FS.writeFile path <| toJson a |>.pretty

open Lake

/-- Returns the root modules of `lean_exe` or `lean_lib` default targets in the Lake workspace. -/
def resolveDefaultRootModules : IO (Array Name) := do
  -- Load the Lake workspace
  let (elanInstall?, leanInstall?, lakeInstall?) ← findInstall?
  let config ← MonadError.runEIO <| mkLoadConfig { elanInstall?, leanInstall?, lakeInstall? }
  let workspace ← MonadError.runEIO <| MainM.runLogIO (loadWorkspace config)

  -- resolve the default build specs from the Lake workspace in similar fashion to `lake build`
  let defaultBuildSpecs ← match resolveDefaultPackageTarget workspace workspace.root with
    | Except.error e => IO.eprintln s!"Error getting default package target: {e}" *> IO.Process.exit 1
    | Except.ok targets => pure targets

  -- build a list of all root modules of `lean_exe` and `lean_lib` build targets
  let defaultTargetModules := defaultBuildSpecs.concatMap <|
    fun target => match target.info with
      | BuildInfo.libraryFacet lib _ => lib.roots
      | BuildInfo.leanExe exe => #[exe.config.root]
      | _ => #[]
  return defaultTargetModules

/--
Parse update and module arguments for `runLinter`

Throws an exception if unable to parse the module argument.
Returns `none` if no module is specified.-/
def parseLinterArgs (args: List String) : Bool × Except String (Option Name) :=
  let (update, moreArgs) :=
    match args with
    | "--update" :: args => (true, args)
    | _ => (false, args)
  let specifiedModule : Except String (Option Name) := match moreArgs with
    | [] => Except.ok none
    | [mod] => match mod.toName with
      | .anonymous => Except.error "cannot convert module to Name"
      | name => Except.ok (some name)
    | _ => Except.error "too many arguments"
  (update, specifiedModule)

/--
Return an array of the modules to lint.

If `specifiedModule` is not `none` return an array containing only `specifiedModule`.
Otherwise, get resolve the default root modules from the Lake workspace -/
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

/--
Usage: `runLinter [--update] [Batteries.Data.Nat.Basic]`

Runs the linters on all declarations in the given module
(or all root modules of Lake default targets by default).
If `--update` is set, the `nolints` file is updated to remove any declarations that no longer need
to be nolinted.
-/
unsafe def main (args : List String) : IO Unit := do
  let (update, specifiedModule) := parseLinterArgs args

  let modulesToLint ← match specifiedModule with
  -- if arg parsing the specified module threw an exception, log it out and exit
  | Except.error msg => IO.eprintln s!"Error: {msg}. Usage: runLinter [--update] [Batteries.Data.Nat.Basic]" *> IO.Process.exit 1
  -- if arg parsing was successful use the specified module to determine the modules to lint
  | Except.ok specifiedModule => determineModulesToLint specifiedModule

  modulesToLint.forM fun module => do
    searchPathRef.set compile_time_search_path%
    let mFile ← findOLean module
    unless (← mFile.pathExists) do
      -- run `lake build module` (and ignore result) if the file hasn't been built yet
      let child ← IO.Process.spawn {
        cmd := (← IO.getEnv "LAKE").getD "lake"
        args := #["build", s!"+{module}"]
        stdin := .null
      }
      _ ← child.wait
    let nolintsFile : FilePath := "scripts/nolints.json"
    let nolints ← if ← nolintsFile.pathExists then
      readJsonFile NoLints nolintsFile
    else
      pure #[]
    withImportModules #[{module}] {} (trustLevel := 1024) fun env =>
      let ctx := { fileName := "", fileMap := default }
      let state := { env }
      Prod.fst <$> (CoreM.toIO · ctx state) do
        let decls ← getDeclsInPackage module.getRoot
        let linters ← getChecks (slow := true) (useOnly := false)
        let results ← lintCore decls linters
        if update then
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
          println!"-- Linting passed for {module}."

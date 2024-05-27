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

/-- Returns the root modules of all `lean_exe` default targets in a Lake workspace. -/
def getDefaultExeRoots (workspace : Workspace) : Array Name :=
  workspace.root.leanExes.filter (fun exe => workspace.root.defaultTargets.contains exe.name)
    |>.map (·.config.root)

/-- Returns the root modules of all `lean_lib` default targets in a Lake workspace. -/
def getDefaultLibRoots (workspace : Workspace) : Array Name :=
  workspace.root.leanLibs.filter (fun lib => workspace.root.defaultTargets.contains lib.name)
    |>.map (·.roots) |>.flatten

/-- Returns the root modules of `lean_exe` or `lean_lib` default targets in the Lake workspace. -/
def getDefaultRootModules : IO (Array Name) := do
  -- Load the Lake workspace
  let (elanInstall?, leanInstall?, lakeInstall?) ← findInstall?
  let config ← MonadError.runEIO <| mkLoadConfig { elanInstall?, leanInstall?, lakeInstall? }
  let workspace ← MonadError.runEIO <| MainM.runLogIO (loadWorkspace config)

  -- return the root modules
  return (getDefaultExeRoots workspace) ++ (getDefaultLibRoots workspace)

/-- Runs the linter on `module`. -/
unsafe def runLinter (update : Bool) (module : Name): IO Unit := do
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

/--
Parse the specified module from args.

Throws an exception if unable to parse the arguments.
Returns `none` if no module is specified.-/
def parseSpecifiedModule (args: List String) : Except String (Option Name) :=
  match args with
    | [] => Except.ok none
    | [mod] => match mod.toName with
      | .anonymous => throw "cannot convert module to Name"
      | name => Except.ok (some name)
    | _ => throw "too many arguments"

/--
Usage: `runLinter [--update] [Batteries.Data.Nat.Basic]`

Runs the linters on all declarations in the given module
(or all root modules of Lake default targets by default).
If `--update` is set, the `nolints` file is updated to remove any declarations that no longer need
to be nolinted.
-/
unsafe def main (args : List String) : IO Unit := do
  let (update, args) :=
    match args with
    | "--update" :: args => (true, args)
    | _ => (false, args)
  match parseSpecifiedModule args with
   | .error msg => IO.eprintln s!"Error: {msg}. Usage: runLinter [--update] [Batteries.Data.Nat.Basic]" *> IO.Process.exit 1
   | .ok module? =>
      match module? with
       | some module =>
          println!"Running linter on specified module: {module}"
          runLinter update module
       | none =>
          println!"Automatically detecting modules to lint"
          let defaultRootModules ← getDefaultRootModules
          println!"running linter on default root modules: {defaultRootModules}"
          Array.forM (runLinter update) defaultRootModules

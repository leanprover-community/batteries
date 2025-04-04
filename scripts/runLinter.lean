import Lean.Util.SearchPath
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

/--
Parse args list for `runLinter`
and return a pair of the update and specified module arguments.

Throws an exception if unable to parse the arguments.
Returns `none` for the specified module if no module is specified.-/
def parseLinterArgs (args: List String) : Except String (Bool × Option Name) :=
  let (update, moreArgs) :=
    match args with
    | "--update" :: args => (true, args)
    | _ => (false, args)
  match moreArgs with
    | [] => Except.ok (update, none)
    | [mod] => match mod.toName with
      | .anonymous => Except.error "cannot convert module to Name"
      | name => Except.ok (update, some name)
    | _ => Except.error "cannot parse arguments"

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
unsafe def runLinterOnModule (update : Bool) (module : Name): IO Unit := do
  initSearchPath (← findSysroot)
  let mFile ← findOLean module
  unless (← mFile.pathExists) do
    -- run `lake build module` (and ignore result) if the file hasn't been built yet
    let child ← IO.Process.spawn {
      cmd := (← IO.getEnv "LAKE").getD "lake"
      args := #["build", s!"+{module}"]
      stdin := .null
    }
    _ ← child.wait
  -- If the linter is being run on a target that doesn't import `Batteries.Tactic.List`,
  -- the linters are ineffective. So we import it here.
  let lintModule := `Batteries.Tactic.Lint
  let lintFile ← findOLean lintModule
  unless (← lintFile.pathExists) do
    -- run `lake build +Batteries.Tactic.Lint` (and ignore result) if the file hasn't been built yet
    let child ← IO.Process.spawn {
      cmd := (← IO.getEnv "LAKE").getD "lake"
      args := #["build", s!"+{lintModule}"]
      stdin := .null
    }
    _ ← child.wait
  let nolintsFile : FilePath := "scripts/nolints.json"
  let nolints ← if ← nolintsFile.pathExists then
    readJsonFile NoLints nolintsFile
  else
    pure #[]
  unsafe Lean.enableInitializersExecution
  let env ← importModules #[module, lintModule] {} (trustLevel := 1024) (loadExts := true)
  let ctx := { fileName := "", fileMap := default }
  let state := { env }
  Prod.fst <$> (CoreM.toIO · ctx state) do
    let decls ← getDeclsInPackage module.getRoot
    let linters ← getChecks (slow := true) (runAlways := none) (runOnly := none)
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
      IO.println s!"-- Linting passed for {module}."

/--
Usage: `runLinter [--update] [Batteries.Data.Nat.Basic]`

Runs the linters on all declarations in the given module
(or all root modules of Lake `lean_lib` and `lean_exe` default targets if no module is specified).
If `--update` is set, the `nolints` file is updated to remove any declarations that no longer need
to be nolinted.
-/
unsafe def main (args : List String) : IO Unit := do
  let linterArgs := parseLinterArgs args
  let (update, specifiedModule) ← match linterArgs with
    | Except.ok args => pure args
    | Except.error msg => do
      IO.eprintln s!"Error parsing args: {msg}"
      IO.eprintln "Usage: runLinter [--update] [Batteries.Data.Nat.Basic]"
      IO.Process.exit 1

  let modulesToLint ← determineModulesToLint specifiedModule

  modulesToLint.forM <| runLinterOnModule update

import Std.Tactic.Lint
import Std.Data.Array.Basic
import Std.Lean.Util.Path

open Lean Core Elab Command Std.Tactic.Lint

/-- The list of `nolints` pulled from the `nolints.json` file -/
abbrev NoLints := Array (Name × Name)

/-- Read the given file path and deserialize it as JSON. -/
def readJsonFile (α) [FromJson α] (path : System.FilePath) : IO α := do
  let _ : MonadExceptOf String IO := ⟨throw ∘ IO.userError, fun x _ => x⟩
  liftExcept <| fromJson? <|← liftExcept <| Json.parse <|← IO.FS.readFile path

/-- Serialize the given value `a : α` to the file as JSON. -/
def writeJsonFile [ToJson α] (path : System.FilePath) (a : α) : IO Unit :=
  IO.FS.writeFile path <| toJson a |>.pretty

/--
Usage: `runLinter [--update] [Std.Data.Nat.Basic]`

Runs the linters on all declarations in the given module (or `Std` by default).
If `--update` is set, the `nolints` file is updated to remove any declarations that no longer need
to be nolinted.
-/
unsafe def main (args : List String) : IO Unit := do
  let (update, args) :=
    match args with
    | "--update" :: args => (true, args)
    | _ => (false, args)
  let some module :=
      match args with
      | [] => some `Std
      | [mod] => Syntax.decodeNameLit s!"`{mod}"
      | _ => none
    | IO.eprintln "Usage: runLinter [--update] [Std.Data.Nat.Basic]" *> IO.Process.exit 1
  let nolintsFile := "scripts/nolints.json"
  let nolints ← readJsonFile NoLints nolintsFile
  searchPathRef.set compile_time_search_path%
  withImportModules #[{module}] {} (trustLevel := 1024) fun env =>
    let ctx := {fileName := "", fileMap := default}
    let state := {env}
    Prod.fst <$> (CoreM.toIO · ctx state) do
      let decls ← getDeclsInPackage `Std
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
            "in Std" (runSlowLinters := true) .medium linters.size
        IO.print (← fmtResults.toString)
        IO.Process.exit 1
      else
        IO.println "-- Linting passed."

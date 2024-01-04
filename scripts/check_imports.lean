/-
Copyright (c) 2024 Joe Hendrix. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joe Hendrix
-/
import Std

/-!
This test checks that all directories in `Std/Data/` have corresponding
`Std.Data.<dir>` modules imported by `Std` that import all of the submodules
under that directory.

It will also check that `Std` imports all the expected modules.

It has a flag (`autofix` below) to automatically fix the errors found.  This
command may need to be rerun to fix all errors; it tries to avoid overwriting
existing files.
-/

open Lean System

/-- Monad to log errors to stderr while record error count. -/
abbrev LogIO := StateRefT (Bool × Bool) IO

def runLogIO (act : LogIO Unit) : MetaM Unit := do
  let ((), (warnings, _)) ← act.run (false, false)
  if warnings then
    throwError "Fatal error"

def warn (fixable : Bool) (msg : String) : LogIO Unit := do
  modify (fun (_, u) => (true, u || not fixable))
  liftM (IO.eprintln msg)

-- | Predicate indicates if warnings are present and if they fixable.
def getWarningInfo : LogIO (Bool × Bool) :=  get

def createModuleHashmap (env : Environment) : HashMap Name ModuleData := Id.run do
  let mut nameMap := {}
  for i in [0:env.header.moduleNames.size] do
    let nm := env.header.moduleNames[i]!
    let md := env.header.moduleData[i]!
    nameMap := nameMap.insert nm md
  pure nameMap

/-- Get the imports we expect in a directory of `Std.Data`. -/
partial def addModulesIn (recurse : Bool) (prev : Array Name) (root : Name := .anonymous)
    (path : FilePath) : IO (Array Name) := do
  let mut r := prev
  for entry in ← path.readDir do
    if ← entry.path.isDir then
      if recurse then
        r ← addModulesIn recurse r (root.mkStr entry.fileName) entry.path
    else
      let .some mod := FilePath.fileStem entry.fileName
        | continue
      r := r.push (root.mkStr mod)
  pure r

def modulePath (name : Name) : FilePath :=
  let path := name.toString.replace "." FilePath.pathSeparator.toString
  s!"{path}.lean"

def writeImportModule (path : FilePath) (imports : Array Name) : IO Unit := do
  let imports := imports.qsort (·.toString < ·.toString)
  let lines := imports.map (s!"import {·}\n")
  let contents := String.join lines.toList
  IO.println s!"Generating {path}"
  IO.FS.writeFile path contents

/-- Check for imports and return true if warnings issued. -/
def checkMissingImports (modName : Name) (modData : ModuleData) (reqImports : Array Name) :
    LogIO Bool := do
  let names : HashSet Name := HashSet.ofArray (modData.imports.map (·.module))
  let mut warned := false
  for req in reqImports do
    if !names.contains req then
      warn true s!"Missing import {req} in {modName}"
      warned := true
  pure warned

/-- Check directory entry in `Std/Data/` -/
def checkStdDataDir
    (modMap : HashMap Name ModuleData)
    (entry : IO.FS.DirEntry) (autofix : Bool := false) : LogIO Unit := do
  let moduleName := `Std.Data ++ entry.fileName
  let requiredImports ← addModulesIn (recurse := true) #[] (root := moduleName) entry.path
  let .some module := modMap.find? moduleName
    | warn true s!"Could not find {moduleName}; Not imported into Std."
      let path := modulePath moduleName
      -- We refuse to generate imported modules whose path doesn't exist.
      -- The import failure will be fixed later and the file rerun
      if autofix then
        if ← path.pathExists then
          warn false s!"Skipping writing of {moduleName}: rerun after {moduleName} imported."
        else
          writeImportModule path requiredImports
      return
  let hasDecls : Bool := module.constants.size > 0
  if hasDecls then
    warn false
          s!"Expected {moduleName} to not contain additional declarations.\n\
            Declarations should be moved out.\n\
            This error cannot be automatically fixed."
  let warned ← checkMissingImports moduleName module requiredImports
  if autofix && warned && !hasDecls then
    writeImportModule (modulePath moduleName) requiredImports

/-- Compute imports expected by `Std.lean` -/
def expectedStdImports : IO (Array Name) := do
  let mut needed := #[]
  for top in ← FilePath.readDir "Std" do
    if top.fileName == "Data" then
      needed ← addModulesIn (recurse := false) needed `Std.Data top.path
    else
      let nm := `Std
      let rootname := FilePath.withExtension top.fileName ""
      let root :=  nm.mkStr rootname.toString
      if ← top.path.isDir then
        needed ← addModulesIn (recurse := true) needed (root := root) top.path
      else
        needed := needed.push root
  pure needed

def checkStdDataImports : MetaM Unit := do
  -- N.B. This can be used to automatically fix Std.lean as well as
  -- other import files.
  -- It uses an environment variable to do that.
  -- The easiest way to use this is run `./scripts/updateStd.sh.`
  let autofix := (← IO.getEnv "__LEAN_STD_AUTOFIX_IMPORTS").isSome
  let env ← getEnv
  let modMap := createModuleHashmap env
  runLogIO do
    for entry in ← FilePath.readDir ("Std" / "Data") do
      if ← entry.path.isDir then
        checkStdDataDir (autofix := autofix) modMap entry
    let stdImports ← expectedStdImports
    let .some stdMod := modMap.find? `Std
        | warn false "Missing Std module!; Run `lake build`."
    let warned ← checkMissingImports `Std stdMod stdImports
    if autofix && warned then
      writeImportModule "Std.lean" stdImports
    match ← getWarningInfo with
    | (false, _) =>
      pure ()
    | (_, true) =>
      IO.eprintln s!"Found errors that cannot be automatically fixed.\n\
                     Address unfixable issues and rerun lake build && ./scripts/updateStd.sh."
    | _ =>
      if autofix then
        IO.eprintln s!"Found missing imports and attempted fixes.\n\
                       Run lake build && ./scripts/updateStd.sh to verify.\n\
                       Multiple runs may be needed."
      else
        IO.eprintln s!"Found missing imports.\n\
                       Run lake build && ./scripts/updateStd.sh to attempt automatic fixes."

run_meta checkStdDataImports

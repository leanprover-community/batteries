import Std

/-- Monad to log errors to stderr while record error count. -/
abbrev LogIO := StateRefT Nat IO

def runLogIO (act : LogIO Unit) : IO Unit := do
  let ((), warnings) ← act.run 0
  if warnings > 0 then
    throw (IO.userError "Detected {warning} error(s).")

def warn (msg : String) : LogIO Unit := do
  modify (· + 1)
  liftM (IO.eprintln msg)

open Lean
open System

def createModuleHashmap (env : Environment) : HashMap Name ModuleData := Id.run do
  let mut nameMap := {}
  for i in [0:env.header.moduleNames.size] do
    let nm := env.header.moduleNames[i]!
    let md := env.header.moduleData[i]!
    nameMap := nameMap.insert nm md
  pure nameMap

/--
Get the imports we expect in a directory of Std.Data.
-/
partial def addModulesIn (recurse : Bool) (prev : Array Name) (root : Name := .anonymous)  (path : FilePath) :
    IO (Array Name) := do
  let mut r := prev
  for entry in ←path.readDir do
    if ←entry.path.isDir then
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
  let imports := imports.qsort (fun x y => x.toString < y.toString)
  let lines := imports.map (s!"import {·}\n")
  let contents := String.join lines.toList
  IO.FS.writeFile path contents

/--
Check directory entry in Std/Data
-/
def checkStdDataDir
   (modMap : HashMap Name ModuleData)
    (entry : IO.FS.DirEntry) (autofix : Bool := false) : LogIO Unit := do
  let moduleName := `Std.Data ++ Name.mkSimple entry.fileName
  let requiredImports ← addModulesIn (recurse := true) #[] (root := moduleName) entry.path
  let .some module := modMap.find? moduleName | do
        warn s!"Could not find {moduleName}"
        let path := modulePath moduleName
        -- We refuse to generate imported modules whose path doesn't exist.
        -- The import failure will be fixed later and the file rerun
        if autofix then
          if ←path.pathExists then
            warn s!"Skipping writing of {moduleName}: rerun after {moduleName} imported."
          else
            writeImportModule (modulePath moduleName) requiredImports
        return
  let hasDecls : Bool := module.constants.size > 0
  if hasDecls then
    warn s!"Expected {moduleName} to not contain data."
  let names : HashSet Name := HashSet.ofArray (module.imports.map (·.module))
  let mut warned := false
  for req in requiredImports do
    if ! names.contains req then
      warn s!"Missing import {req} in {moduleName}"
      warned := true
  if autofix && warned && !hasDecls then
    writeImportModule (modulePath moduleName) requiredImports

-- Write standard imports if needed.
def writeStdImports : IO Unit := do
  let mut needed := #[]
  for top in ←FilePath.readDir "Std"  do
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
  writeImportModule "Std.lean" needed

/--
This command checks that all directories in Std/Data have corresponding
Std.Data.dir modules imported by `Std` that import all of the submodules
in that diectory.

It has a flag to auto-generate the files if needed.
-/
elab "#checkStdDataImports" : command => do
  -- N.B. Change to true to have the file automatically fix imports.
  -- This feature may overwrite files and should be disabled in commits.
  let autofix := false
  let env ← getEnv
  let modMap := createModuleHashmap env
  Lean.Elab.Command.liftIO $ runLogIO do
    for entry in ←FilePath.readDir ("Std" / "Data")  do
      if ←entry.path.isDir then
        checkStdDataDir (autofix := autofix) modMap entry
    if autofix then
      writeStdImports

#checkStdDataImports

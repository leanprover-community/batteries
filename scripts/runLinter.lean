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
  let defaultTargetModules ← workspace.root.defaultTargets.flatMapM fun target => do
    if let some lib := workspace.root.findLeanLib? target then
      pure <| (← lib.getModuleArray).map Lake.Module.name
    else if let some exe := workspace.root.findLeanExe? target then
      pure #[exe.config.root]
    else
      pure #[]
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
  /-- If set (with `--only-modules=FILE`), a file listing module names, one per line. Local linters
  (`Linter.isLocal`) then lint only the declarations defined in those modules; the other linters
  still lint everything. -/
  onlyModules : Option System.FilePath := none
  /-- If set (with `--write-global-fingerprint=FILE`), write the global-input fingerprint of the
  imported environment to `FILE` before linting. -/
  writeFingerprint : Option System.FilePath := none
  /-- If set (with `--baseline-global-fingerprint=FILE`), compare the global-input fingerprint of
  the imported environment with the one in `FILE`. When they are equal, every linter lints only the
  declarations of the modules listed with `--only-modules`. -/
  baselineFingerprint : Option System.FilePath := none

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
    Except (List String) (LinterConfig × List Name) :=
  go {} [] args
where
  /-- Traverses the list, handling the non-flag elements as modules and erroring if parsing fails. -/
  go (parsed : LinterConfig) (mods: List Name) : List String → Except (List String) (LinterConfig × List Name)
    | arg :: rest =>
      if let some parsed := parseArg parsed arg then
        go parsed mods rest
      else
        match arg.toName with
        | .anonymous => Except.error [s!"could not parse argument '{arg}'"]
        | mod => go parsed (mod :: mods) rest
    | [] => Except.ok (parsed, mods.reverse)

  /-- Parses a single config argument. -/
  parseArg (parsed : LinterConfig) : String → Option LinterConfig
    | "--update"   => some { parsed with updateNoLints := true }
    | "--no-build" => some { parsed with noBuild := true }
    | "--trace"
    | "-v"         => some { parsed with trace := true }
    | arg =>
      if let some file := arg.dropPrefix? "--only-modules=" then
        if file.isEmpty then none else some { parsed with onlyModules := some file.toString }
      else if let some file := arg.dropPrefix? "--write-global-fingerprint=" then
        if file.isEmpty then none else some { parsed with writeFingerprint := some file.toString }
      else if let some file := arg.dropPrefix? "--baseline-global-fingerprint=" then
        if file.isEmpty then none else
          some { parsed with baselineFingerprint := some file.toString }
      else none

/--
Return an array of the modules to lint.

If `specifiedModules` is not empty, return an array containing only `specifiedModule`.
Otherwise, resolve the default root modules from the Lake workspace. -/
def determineModulesToLint (specifiedModules : List Name) : IO (Array Name) := do
  match specifiedModules with
  | [] =>
    println!"Automatically detecting modules to lint"
    let defaultModules ← resolveDefaultRootModules
    println!"Default modules: {defaultModules}"
    return defaultModules
  | modules =>
    println!"Running linter on specified modules: {modules}"
    return modules.toArray

/-!
## Global-input fingerprint

The lint verdict of a declaration depends on its own module and the modules that it imports, and on
global tables that any module can extend: the `simp` set, the instances, and the other tables below.
Every module that imports a changed module is changed too. So when every global table is unchanged,
the verdicts of the declarations in unchanged modules are unchanged, and all linters can be
restricted to the changed modules. The fingerprint hashes each global table over all imported
modules, in import order. A linter that reads another global table must add that table here.
-/

open Meta

/-- The number of entries of a table and a hash over them, in order. -/
structure TableDigest where
  /-- The number of entries. -/
  count : Nat := 0
  /-- The hash over the entries, in order. -/
  hash : UInt64 := 7

/-- Adds the hash of one entry to `d`. -/
def TableDigest.push (d : TableDigest) (h : UInt64) : TableDigest :=
  { count := d.count + 1, hash := mixHash d.hash h }

/-- The digest of one global table, as written to the fingerprint file. -/
structure TableFingerprint where
  /-- The name of the table. -/
  name : String
  /-- The number of entries. -/
  count : Nat
  /-- The hash over the entries, in decimal. -/
  hash : String
  deriving BEq, ToJson, FromJson

/-- The global inputs of the environment linters: the toolchain, the linters that run, the
`nolints` file and one digest per global table. -/
structure GlobalFingerprint where
  /-- The git hash of the Lean toolchain. -/
  lean : String
  /-- The names of the linters that run, in order. -/
  linters : Array String
  /-- The hash of the contents of the `nolints` file, in decimal. -/
  nolints : String
  /-- The digests of the global tables. -/
  tables : Array TableFingerprint
  deriving BEq, ToJson, FromJson

/-- Combines the hashes `hs` in order. -/
def mixAll (hs : List UInt64) : UInt64 := hs.foldl mixHash 7

/-- The hash of the type of the constant `n`, or `0` if the environment does not contain it. -/
def typeHash (env : Environment) (n : Name) : UInt64 :=
  match env.find? n with
  | some ci => ci.type.hash
  | none => 0

/-- The hash of the value of the constant `n`, or `0` if the environment holds no value for it. -/
def valueHash (env : Environment) (n : Name) : UInt64 :=
  match env.find? n with
  | some ci => match ci.value? (allowOpaque := true) with
    | some v => v.hash
    | none => 0
  | none => 0

/-- Hashes `f e` for every exported entry `e` of `ext`, over all imported modules in import order. -/
def digestEntries [Inhabited σ] (env : Environment) (ext : PersistentEnvExtension α β σ)
    (f : α → UInt64) : TableDigest := Id.run do
  let mut d : TableDigest := {}
  for i in [:env.header.moduleNames.size] do
    for e in ext.getModuleEntries env i do
      d := d.push (f e)
  return d

/-- Hashes an entry of a scoped extension, including the namespace of a scoped entry. -/
def scopedEntryHash (f : α → UInt64) : ScopedEnvExtension.Entry α → UInt64
  | .global a => mixHash 0 (f a)
  | .scoped ns a => mixHash (hash ns) (f a)

/-- Hashes a `simp` set entry: its attributes and the statement that it rewrites with. -/
def simpEntryHash (env : Environment) : SimpEntry → UInt64
  | .thm t =>
    let stmt := match t.origin with
      | .decl n .. => typeHash env n
      | _ => t.proof.hash
    mixAll [1, hash t.origin, hash t.priority, hash t.post, hash t.perm, hash t.rfl,
      hash t.backwardRfl, stmt]
  | .toUnfold n => mixAll [2, hash n, valueHash env n]
  | .toUnfoldThms n thms => mixAll [3, hash n, valueHash env n, hash thms]

/-- Hashes a reducibility entry. The value of a definition that unfolds at reducible or instance
transparency is part of the entry. -/
def reducibilityHash (env : Environment) : Name × ReducibilityStatus → UInt64
  | (n, s) =>
    let value := match s with
      | .semireducible | .irreducible => 0
      | _ => valueHash env n
    mixAll [hash n, hash s.toAttrString, value]

open Lean.Parser.Tactic.Doc in
/-- Computes the global-input fingerprint of the current environment. -/
def globalFingerprint (linters : Array NamedLinter) (nolints : String) :
    CoreM GlobalFingerprint := do
  let env ← getEnv
  let tables : Array (String × TableDigest) := #[
    ("simp", digestEntries env simpExtension.ext (scopedEntryHash (simpEntryHash env))),
    ("congr", digestEntries env congrExtension.ext <| scopedEntryHash fun t =>
      mixAll [hash t.theoremName, hash t.funName, hash t.hypothesesPos, hash t.priority,
        typeHash env t.theoremName]),
    ("instances", digestEntries env instanceExtension.ext <| scopedEntryHash fun e =>
      mixAll [hash e.globalName?, hash e.priority, hash e.synthOrder, hash (toString e.attrKind),
        e.val.hash, e.globalName?.elim 0 (typeHash env), e.globalName?.elim 0 (valueHash env)]),
    ("defaultInstances", digestEntries env defaultInstanceExtension fun e =>
      mixAll [hash e.className, hash e.instanceName, hash e.priority]),
    ("classes", digestEntries env classExtension fun e =>
      mixAll [hash e.name, hash e.outParams, hash e.outLevelParams]),
    ("reducibility", digestEntries env reducibilityCoreExt (reducibilityHash env)),
    ("reducibilityExtra",
      digestEntries env reducibilityExtraExt.ext (scopedEntryHash (reducibilityHash env))),
    ("unificationHints", digestEntries env unificationHintExtension.ext <| scopedEntryHash fun e =>
      mixAll [hash e.val, valueHash env e.val]),
    ("tacticDocExtensions", digestEntries env tacticDocExtExt fun (n, docs) =>
      mixAll [hash n, hash docs]),
    ("tacticAlternatives", digestEntries env tacticAlternativeExt fun (n, alt) =>
      mixAll [hash n, hash alt]),
    ("tacticNames", digestEntries env tacticNameExt fun (n, name) => mixAll [hash n, hash name])]
  return {
    lean := Lean.githash
    linters := linters.map (·.name.toString)
    nolints := toString (hash nolints)
    tables := tables.map fun (name, d) =>
      { name, count := d.count, hash := toString d.hash } }

/-- The names of the parts of `current` that differ from `baseline`, or the reason why `baseline`
cannot be read. An empty array means that the two fingerprints are equal. -/
def fingerprintDifferences (baseline : FilePath) (current : GlobalFingerprint) :
    IO (Array String) := do
  let base ← try readJsonFile GlobalFingerprint baseline catch e =>
    return #[s!"the baseline cannot be read ({e})"]
  let mut diffs := #[]
  if base.lean != current.lean then diffs := diffs.push "lean"
  if base.linters != current.linters then diffs := diffs.push "linters"
  if base.nolints != current.nolints then diffs := diffs.push "nolints"
  for t in current.tables do
    unless base.tables.contains t do diffs := diffs.push t.name
  for t in base.tables do
    unless current.tables.any (·.name == t.name) do diffs := diffs.push t.name
  return diffs

/--
Run the Batteries linter on `module`. If `cfg.updateNoLints` is `true`, update the nolints file.

If `leakEnv` is `true`, mark the imported environment as persistent. Lean then never frees the
environment, so set `leakEnv` only when the process exits after the lint.
-/
unsafe def runLinterOnModule (cfg : LinterConfig) (module : Name)
    (leakEnv := false) : IO Unit := do
  let { updateNoLints, noBuild, trace, onlyModules, writeFingerprint, baselineFingerprint } := cfg
  if updateNoLints && onlyModules.isSome then
    IO.eprintln "--update cannot be combined with --only-modules: \
      it would rewrite the nolints file from a partial run"
    IO.Process.exit 1
  if baselineFingerprint.isSome && onlyModules.isNone then
    IO.eprintln "--baseline-global-fingerprint requires --only-modules"
    IO.Process.exit 1
  initSearchPath (← findSysroot)
  let rec
    /-- Builds `module` if the filepath `olean` does not exist. Throws if olean is not found and
    `noBuild := true`. -/
    buildIfNeeded (module : Name) : IO Unit := do
      let olean ← findOLean module
      unless (← olean.pathExists) do
        if noBuild then
          IO.eprintln s!"[{module}] Could not find olean for module `{module}` at given path:\n  \
            {olean}"
          IO.Process.exit 1
        else
          if trace then
            IO.println s!"[{module}] Could not find olean for module `{module}` at given path:\n  \
              {olean}\n\
              [{module}] Building `{module}`."
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
  let nolintsText ← if ← nolintsFile.pathExists then IO.FS.readFile nolintsFile else pure ""
  let nolints ← if nolintsText.isEmpty then pure #[] else
    readJsonFile NoLints nolintsFile
  unsafe Lean.enableInitializersExecution
  let env ← importModules #[module, lintModule] {} (trustLevel := 1024)
    (loadExts := true) (leakEnv := leakEnv)
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
    let fingerprint ← if writeFingerprint.isSome || baselineFingerprint.isSome then
      some <$> globalFingerprint linters nolintsText
    else
      pure none
    if let (some file, some fp) := (writeFingerprint, fingerprint) then
      writeJsonFile file fp
      IO.println s!"[{module}] Wrote the global-input fingerprint to {file}."
    -- `lintDecls` are the declarations that the linters lint. When the global-input fingerprint
    -- matches the baseline, these are the declarations of the listed modules; otherwise only the
    -- local linters lint `localDecls`.
    let (lintDecls, localDecls, scope) ← match onlyModules with
      | none => pure (decls, none, "")
      | some file =>
        let env ← getEnv
        let listed := (← IO.FS.lines file).map (·.trimAscii.copy) |>.filter (!·.isEmpty)
          |>.map (·.toName)
        -- Modules that are not in the environment (for example, deleted files) are skipped, but
        -- always reported: a typo would otherwise silently narrow the lint.
        let missing := listed.filter (env.getModuleIdx? · |>.isNone)
        unless missing.isEmpty do
          IO.println s!"[{module}] --only-modules: {missing.size} listed module(s) are not in the \
            environment and are skipped: {missing.toList}"
        let idxs := listed.filterMap env.getModuleIdx?
        let restricted := decls.filter fun d => (env.getModuleIdxFor? d).any idxs.contains
        let diffs ← match baselineFingerprint, fingerprint with
          | some base, some fp => do
            let diffs ← fingerprintDifferences base fp
            if diffs.isEmpty then
              IO.println s!"[{module}] The global-input fingerprint matches the baseline {base}."
            else
              IO.println s!"[{module}] The global-input fingerprint differs from the baseline \
                {base} in: {", ".intercalate diffs.toList}."
            pure diffs
          | _, _ => pure #["no baseline"]
        if diffs.isEmpty then
          IO.println s!"[{module}] --only-modules: all {linters.size} linters lint the \
            {restricted.size} declarations of {idxs.size} listed modules."
          pure (restricted, none,
            s!" (all linters: only the {restricted.size} declarations of the listed modules)")
        else
          let nLocal := (linters.filter (·.isLocal)).size
          IO.println s!"[{module}] --only-modules: {nLocal} local linters lint the \
            {restricted.size} declarations of {idxs.size} listed modules; the other \
            {linters.size - nLocal} lint all {decls.size} declarations."
          pure (decls, some restricted,
            s!" (local linters: only the {restricted.size} declarations of the listed modules)")
    let results ← lintCore lintDecls linters (inIO := true) (currentModule := module)
      (localDecls := localDecls)
    if updateNoLints then
      traceLint s!"Updating nolints file at {nolintsFile}" (inIO := true) (currentModule := module)
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
      IO.println s!"[{module}] {nolintsFile} summary (number of nolints per linter):\n  \
        {"\n  ".intercalate msgs}"
    let results := results.map fun (linter, decls) =>
      .mk linter <| nolints.foldl (init := decls) fun decls (linter', decl') =>
        if linter.name == linter' then decls.erase decl' else decls
    let failed := results.any (!·.2.isEmpty)
    if failed then
      let fmtResults ←
        formatLinterResults results lintDecls (groupByFilename := true) (useErrorFormat := true)
          s!"in {module}{scope}" (runSlowLinters := true) .medium linters.size
      IO.print (← fmtResults.toString)
      IO.Process.exit 1
    else
      IO.println s!"-- Linting passed for {module}."

/--
Usage: `runLinter [--update] [--trace | -v] [--no-build] [--only-modules=FILE]
  [--baseline-global-fingerprint=FILE] [--write-global-fingerprint=FILE]
  [Batteries.Data.Nat.Basic]...`

Runs the linters on all declarations in the given modules
(or all root modules of Lake `lean_lib` and `lean_exe` default targets if no module is specified).

If `--update` is set, the `nolints` file is updated to remove any declarations that no longer need
to be nolinted.

If `--trace` (or, synonymously, `-v`) is set, tracing will be enabled and logged to stdout.

If `--no-build` is set, `runLinter` will throw if either the oleans to be linted or the oleans
which drive the linting itself are not present.

If `--only-modules=FILE` is set, where `FILE` lists module names one per line, local linters
(`Linter.isLocal`) lint only the declarations defined in those modules, for example to lint only
the files a pull request changed; the other linters, such as `simpNF`, still lint every
declaration. Listed modules that are not in the environment are skipped and reported.
`--only-modules` cannot be combined with `--update`. It is only sound for changes to ordinary
modules: a caller must lint everything when a linter's own code or `nolints.json` changes.

If `--write-global-fingerprint=FILE` is set, `runLinter` writes to `FILE` a fingerprint of the
global inputs of the linters before it lints: the toolchain, the linters that run, the `nolints`
file, and the global tables that any module can extend, such as the `simp` set and the instances.
It combines with every other option, for example to record a baseline during a full lint.

If `--baseline-global-fingerprint=FILE` is set together with `--only-modules`, `runLinter` compares
the fingerprint of the environment with the one in `FILE`. When they are equal, every linter, the
non-local ones included, lints only the declarations of the listed modules. This is sound when the
listed modules include every module whose content or imports differ from the baseline's
environment. When the fingerprints differ, `--only-modules` restricts only the local linters.
Each fingerprint option takes exactly one module.
-/
unsafe def main (args : List String) : IO Unit := do
  let linterArgs := parseLinterArgs args
  let (cfg, mods) ← match linterArgs with
    | Except.ok args => pure args
    | Except.error msgs => do
      IO.eprintln s!"Error parsing args:\n  {"\n  ".intercalate msgs}"
      IO.eprintln "Usage: \
        runLinter [--update] [--trace | -v] [--no-build] [--only-modules=FILE] \
        [--baseline-global-fingerprint=FILE] [--write-global-fingerprint=FILE] \
        [Batteries.Data.Nat.Basic]..."
      IO.Process.exit 1

  let modulesToLint ← determineModulesToLint mods
  if (cfg.writeFingerprint.isSome || cfg.baselineFingerprint.isSome) && modulesToLint.size != 1 then
    IO.eprintln s!"--write-global-fingerprint and --baseline-global-fingerprint take exactly one \
      module, not {modulesToLint.size}"
    IO.Process.exit 1

  -- With one module, the imported environment stays in memory until the process exits. Mark it
  -- as persistent to avoid atomic reference-count updates when the lint tasks share it.
  -- With several modules, keep the default so that each environment is freed before the next
  -- import.
  let leakEnv := modulesToLint.size == 1
  modulesToLint.forM fun module => runLinterOnModule cfg module (leakEnv := leakEnv)
  -- TODO: Remove manual Process.exit
  -- We are doing this to shortcut around a race in Lean's IO finalizers that we have observed in Mathlib CI
  -- (https://leanprover.zulipchat.com/#narrow/channel/287929-mathlib4/topic/slow.20linting.20step.20CI.3F/with/568830914)
  IO.Process.exit 0

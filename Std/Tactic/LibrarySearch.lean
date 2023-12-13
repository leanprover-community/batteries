/-
Copyright (c) 2021 Gabriel Ebner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner, Scott Morrison
-/
import Std.Lean.CoreM
import Std.Lean.Expr
import Std.Lean.Meta.DiscrTree
import Std.Lean.Meta.LazyDiscrTree
import Std.Tactic.SolveByElim
import Std.Util.Pickle

/-!
# Library search

This file defines tactics `exact?` and `apply?`,
(formerly known as `library_search`)
and a term elaborator `exact?%`
that tries to find a lemma
solving the current goal
(subgoals are solved using `solveByElim`).

```
example : x < x + 1 := exact?%
example : Nat := by exact?
```
-/

namespace Std.Tactic.LibrarySearch

open Lean Meta Std.Tactic.TryThis

initialize registerTraceClass `Tactic.stdLibrarySearch
initialize registerTraceClass `Tactic.stdLibrarySearch.lemmas

/-- Configuration for `DiscrTree`. -/
def discrTreeConfig : WhnfCoreConfig := {}

/--
A "modifier" for a declaration.
* `none` indicates the original declaration,
* `mp` indicates that (possibly after binders) the declaration is an `↔`,
  and we want to consider the forward direction,
* `mpr` similarly, but for the backward direction.
-/
inductive DeclMod
  | /-- the original declaration -/ none
  | /-- the forward direction of an `iff` -/ mp
  | /-- the backward direction of an `iff` -/ mpr
deriving DecidableEq, Inhabited, Ord

instance : ToString DeclMod where
  toString m := match m with | .none => "" | .mp => "mp" | .mpr => "mpr"

/--
LibrarySearch has an extension mechanism for replacing the function used
to find candidate lemmas.
-/
@[reducible]
def CandidateFinder := Expr → MetaM (Array (Name × DeclMod))

namespace DiscrTreeFinder

open System (FilePath)

/--
An even wider class of "internal" names than reported by `Name.isInternalDetail`.
-/
-- from Lean.Server.Completion
private def isBlackListed (env : Environment) (declName : Name) : Bool :=
  declName == ``sorryAx
  || declName.isInternalDetail
  || declName matches .str _ "inj"
  || declName matches .str _ "noConfusionType"
  || isAuxRecursor env declName
  || isNoConfusion env declName
  || isRecCore env declName
  || isMatcherCore env declName

/--
Once we reach Mathlib, and have `cache` available,
it will be essential that we load a precomputed cache for `exact?` from a `.olean` file.

This makes no sense here in Std, where there is no caching mechanism.
-/
def cachePath : IO FilePath := do
  let sp ← searchPathRef.get
  if let buildPath :: _ := sp then
    let path := buildPath / "LibrarySearch.extra"
    if ← path.pathExists then
      return path
  return ".lake" / "build" / "lib" / "LibrarySearch.extra"

/-- Add a path to a discrimination tree.-/
private def addPath [BEq α] (config : WhnfCoreConfig) (tree : DiscrTree α) (tp : Expr) (v : α) :
    MetaM (DiscrTree α) := do
  let k ← DiscrTree.mkPath tp config
  pure <| tree.insertCore k v config

/-- Adds a constant with given name to tree. -/
private def updateTree (config : WhnfCoreConfig) (tree : DiscrTree (Name × DeclMod))
    (name : Name) (constInfo : ConstantInfo) : MetaM (DiscrTree (Name × DeclMod)) := do
  if constInfo.isUnsafe then return tree
  if isBlackListed (←getEnv) name then return tree
  withReducible do
    let (_, _, type) ← forallMetaTelescope constInfo.type
    let tree ← addPath config tree type (name, DeclMod.none)
    match type.getAppFnArgs with
    | (``Iff, #[lhs, rhs]) => do
      let tree ← addPath config tree rhs (name, DeclMod.mp)
      let tree ← addPath config tree lhs (name, DeclMod.mpr)
      return tree
    | _ =>
      return tree

/--
Constructs an discriminator tree from the current environment.
-/
def buildImportCache (config : WhnfCoreConfig) : MetaM (DiscrTree (Name × DeclMod)) := do
  let profilingName := "apply?: init cache"
  -- Sort so lemmas with longest names come first.
  -- This is counter-intuitive, but the way that `DiscrTree.getMatch` returns results
  -- means that the results come in "batches", with more specific matches *later*.
  -- Thus we're going to call reverse on the result of `DiscrTree.getMatch`,
  -- so if we want to try lemmas with shorter names first,
  -- we need to put them into the `DiscrTree` backwards.
  let post (A : Array (Name × DeclMod)) :=
        A.map (fun (n, m) => (n.toString.length, n, m)) |>.qsort (fun p q => p.1 > q.1) |>.map (·.2)
  profileitM Exception profilingName (← getOptions) do
    (·.mapArrays post) <$> (← getEnv).constants.map₁.foldM (init := {}) (updateTree config)

/--
Return matches from local constants.

N.B. The efficiency of this could likely be considerably improved by caching in environment
extension.
-/
def localMatches (config : WhnfCoreConfig) (ty : Expr) : MetaM (Array (Name × DeclMod)) := do
  let locals ← (← getEnv).constants.map₂.foldlM (init := {}) (DiscrTreeFinder.updateTree config)
  pure <| (← locals.getMatch  ty config).reverse

/--
Candidate finding function that uses strict discrimination tree for resolution.
-/
def mkImportFinder (config : WhnfCoreConfig) (importTree : DiscrTree (Name × DeclMod))
    (ty : Expr) : MetaM (Array (Name × DeclMod)) := do
  pure <| (← importTree.getMatch ty config).reverse

end DiscrTreeFinder

namespace IncDiscrTreeFinder

open DiscrTreeFinder (isBlackListed)

/--
This is a monad for building initial discrimination tree.
-/
@[reducible]
private def TreeInitM := StateT (LazyDiscrTree (Name × DeclMod)) MetaM

open LazyDiscrTree (Key LazyEntry)

private def libSearchContext : Meta.Context := {
    config := { transparency := .reducible }
  }

private structure ErrorCollection (ε : Type) (α : Type) where
  value  : α
  errors : Array ε := #[]

instance [Inhabited α] : Inhabited (ErrorCollection ε α) := ⟨{ value := default }⟩


private def ErrorCollection.join (f : α → α → α) (x y : ErrorCollection ε α) : ErrorCollection ε α :=
  let { value := xv, errors := xe } := x
  let { value := yv, errors := ye } := y
  { value := f xv yv, errors := xe ++ ye }

/--
Structure for quickly initializing a lazy tree with a large number of elements.

Designed for efficient insertion and merging multiple discrimination trees.
-/
structure PreDiscrTree (α : Type) where
  /-- Maps keys to index in tries array. -/
  roots : HashMap Key Nat := {}
  /-- Lazy entries for root of treie-/
  tries : Array (Array (LazyEntry α)) := #[]
  deriving Inhabited

namespace PreDiscrTree

private def modifyAt (d : PreDiscrTree α) (k : Key)
    (f : Array (LazyEntry α) → Array (LazyEntry α)) : PreDiscrTree α :=
  let { roots, tries } := d
  match roots.find? k with
  | .none =>
    let roots := roots.insert k tries.size
    { roots, tries := tries.push (f #[]) }
  | .some i =>
    { roots, tries := tries.modify i f }

/-- Add an entries to the pre-discrimination tree.-/
def push (d : PreDiscrTree α) (k : Key) (e : LazyEntry α) : PreDiscrTree α :=
  d.modifyAt k (·.push e)

/-- Convert a pre-discrimination tree to a lazy discrimination tree. -/
def toTree (d : PreDiscrTree α) (config : WhnfCoreConfig := {}) : LazyDiscrTree α :=
  let { roots, tries } := d
  { config, root := roots, array := tries.map (.node {} 0 {}) }

/-- Merge two discrimination trees. -/
protected def append (x y : PreDiscrTree α) : PreDiscrTree α :=
  if x.roots.size ≥ y.roots.size then
    aux x y (fun y x => x ++ y)
  else
    aux y x (fun x y => y ++ x)
  where aux x y (f : Array (LazyEntry α) → Array (LazyEntry α) → Array (LazyEntry α)) :=
    let { roots := yk, tries := ya } := y
    yk.fold (init := x) fun d k yi => d.modifyAt k (f ya[yi]!)

instance : Append (PreDiscrTree α) where
  append := PreDiscrTree.append

end PreDiscrTree

private def pushEntry (r : IO.Ref (PreDiscrTree α)) (lctx : LocalContext × LocalInstances) (type : Expr)
    (v : α) : MetaM Unit := do
  let (k, todo) ← LazyDiscrTree.rootKey' {} type
  r.modify (·.push k (todo, lctx, v))

/-- Information generation from imported modules. -/
private structure ImportData where
  cache : IO.Ref (Lean.Meta.Cache)
  data : IO.Ref (PreDiscrTree (Name × DeclMod))
  errors : IO.Ref (Array (Name × Name))

private def ImportData.new : BaseIO ImportData := do
  let cache ← IO.mkRef {}
  let data ← IO.mkRef {}
  let errors ← IO.mkRef #[]
  pure { cache, data, errors }

private def addConstImportData (env : Environment) (modName : Name) (d : ImportData)
    (name : Name) (constInfo : ConstantInfo) : BaseIO Unit := do
  if constInfo.isUnsafe then return ()
  if isBlackListed env name then return ()
  let mstate : Meta.State := { cache := ←d.cache.get }
  d.cache.set {}
  let mm : MetaM Unit :=
        forallTelescope constInfo.type fun _ type => do
          let lctx ← getLCtx
          let linst ← Lean.Meta.getLocalInstances
          let lctx := (lctx, linst)
          let (k, todo) ← LazyDiscrTree.rootKey' {} type
          d.data.modify (·.push k (todo, lctx, (name, DeclMod.none)))
          let biff := k == DiscrTree.Key.const ``Iff 2
          if biff then
            pushEntry d.data lctx todo[0]! (name, DeclMod.mp)
            pushEntry d.data lctx todo[1]! (name, DeclMod.mpr)
          else
            pure ()
  let cm : CoreM (Unit × _) := mm.run libSearchContext mstate
  let cctx : Core.Context := {
    fileName := default,
    fileMap := default
  }
  let cstate : Core.State := {env}
  match ←(cm.run cctx cstate).toBaseIO with
  | .ok (((), ms), _) =>
    d.cache.set ms.cache
  | .error _ =>
    d.errors.modify (·.push (modName, name))

private partial def loadImportedModule (env : Environment)
    (d : ImportData)
    (mname : Name)
    (mdata : ModuleData) (i : Nat := 0) : BaseIO Unit := do
  if h : i < mdata.constNames.size then
    let nm := mdata.constNames[i]
    let c  := mdata.constants[i]!
    addConstImportData env mname d nm c
    loadImportedModule env d mname mdata (i+1)
  else
    pure ()

private def ImportData.toFlat (d : ImportData) :
    BaseIO (ErrorCollection (Name × Name) (PreDiscrTree (Name × DeclMod))) := do
  let dm ← d.data.swap {}
  let de ← d.errors.swap #[]
  pure ⟨dm, de⟩


private def createImportedEnvironmentSeq (env : Environment) (start stop : Nat) :
    BaseIO (ErrorCollection (Name × Name) (PreDiscrTree (Name × DeclMod))) :=
      do go (← ImportData.new) start stop
    where go d (start stop : Nat) : BaseIO _ := do
            if start < stop then
              let mname := env.header.moduleNames[start]!
              let mdata := env.header.moduleData[start]!
              loadImportedModule env d mname mdata
              go d (start+1) stop
            else
              d.toFlat
  termination_by go _ idx stop => stop - idx

/--
The maximum number of constants an individual task performed.

The value below was picked because it roughly correponded to 50ms of work on
one of the development machines.
-/
private def constantsPerTask : Nat := 6500

/-- This creates -/
private def launchImportedEnvironment (env : Environment) :
    BaseIO (Array (Task (ErrorCollection (Name × Name) (PreDiscrTree (Name × DeclMod))))) := do
  let n := env.header.moduleData.size
  let rec go tasks start cnt idx := do
        if h : idx < env.header.moduleData.size then
          let mdata := env.header.moduleData[idx]
          let cnt := cnt + mdata.constants.size
          if cnt > constantsPerTask then
            let t ← createImportedEnvironmentSeq env start (idx+1) |>.asTask
            go (tasks.push t) (idx+1) 0 (idx+1)
          else
            go tasks start cnt (idx+1)
        else
          if start < n then
            tasks.push <$> (createImportedEnvironmentSeq env start n).asTask
          else
            pure tasks
  go #[] 0 0 0
  termination_by go _ idx => env.header.moduleData.size - idx

/-- Get the rests of each task and merge using combining function -/
private partial def combineGet (z : α) (f : α → α → α) (tasks : Array (Task α)) : α :=
  tasks.foldl (fun x t => f x t.get) (init := z)

private partial def createImportedEnvironment (opts : Options) (env : Environment) :
    BaseIO (LazyDiscrTree (Name × DeclMod)) := profileitIO "librarySearch launch" opts $ do
  let tasks ← launchImportedEnvironment env
  let r := combineGet default (fun x y => ErrorCollection.join Append.append x y) tasks
  pure <| r.value.toTree

/--
Candidate finding function that uses strict discrimination tree for resolution.
-/
def mkImportFinder : IO CandidateFinder := do
  let ref ← IO.mkRef none
  pure fun ty => do
    let importTree ← (←ref.get).getDM $ do
      createImportedEnvironment (←getOptions) (←getEnv)
    let (imports, importTree) ← importTree.getMatch ty
    ref.set importTree
    pure imports

end IncDiscrTreeFinder

private unsafe def mkImportFinder : IO CandidateFinder := do
  let path ← DiscrTreeFinder.cachePath
  if ← path.pathExists then
    let (imports, _) ← unpickle (DiscrTree (Name × DeclMod)) path
    -- `DiscrTree.getMatch` returns results in batches, with more specific lemmas coming later.
    -- Hence we reverse this list, so we try out more specific lemmas earlier.
    pure <| DiscrTreeFinder.mkImportFinder {} imports
  else do
    IncDiscrTreeFinder.mkImportFinder


/--
Retrieve the current current of lemmas.
-/
initialize defaultCandidateFinder : IO.Ref CandidateFinder ← unsafe do
  IO.mkRef (←mkImportFinder)

/--
Update the candidate finder used by library search.
-/
def setDefaultCandidateFinder (cf : CandidateFinder) : IO Unit :=
  defaultCandidateFinder.set cf

private def emoji (e:Except ε α) := if e.toBool then checkEmoji else crossEmoji

/-- Create lemma from name and mod. -/
def mkLibrarySearchLemma (lem : Name) (mod : DeclMod) : MetaM Expr := do
  let lem ← mkConstWithFreshMVarLevels lem
  match mod with
  | .none => pure lem
  | .mp => mapForallTelescope (fun e => mkAppM ``Iff.mp #[e]) lem
  | .mpr => mapForallTelescope (fun e => mkAppM ``Iff.mpr #[e]) lem

/--
Try applying the given lemma (with symmetry modifier) to the goal,
then try to close subsequent goals using `solveByElim`.
If `solveByElim` succeeds, we return `[]` as the list of new subgoals,
otherwise the full list of subgoals.
-/
def librarySearchLemma (act : List MVarId → MetaM (List MVarId)) (allowFailure : Bool) (goal : MVarId) (lem : Expr) : MetaM (List MVarId) := do
  withTraceNode `Tactic.librarySearch (return m!"{emoji ·} trying {lem}") do
    let newGoals ← goal.apply lem { allowSynthFailures := true }
    try
      act newGoals
    catch _ =>
      if allowFailure then
        pure newGoals
      else
        failure

/--
Returns a lazy list of the results of applying a library lemma,
then calling `solveByElim` on the resulting goals.
-/
def librarySearchCore (searchFn : CandidateFinder) (tgt : Expr) : MetaM (Array Expr) := do
  let candidates ← searchFn tgt
  trace[Tactic.stdLibrarySearch.lemmas] m!"Candidate library_search lemmas:\n{candidates}"
  let mut res := Array.mkEmpty candidates.size
  for (name, mod) in candidates do
    try
      res := res.push (←mkLibrarySearchLemma name mod)
    catch _ =>
      pure ()
  return res

/-- interleave x y interleaves the elements of x and y until one is empty and then returns final elements. -/
def interleave [Inhabited α] (x y : Array α) : Array α := Id.run do
  let mut res := Array.mkEmpty (x.size + y.size)
  let n := min x.size y.size
  for i in [0:n] do
    res := res.push x[i]!
    res := res.push y[i]!
  pure $ res ++ (if x.size > n then x.extract n x.size else y.extract n y.size)

/--
Run `librarySearchCore` on both the goal and `symm` applied to the goal.
-/
def librarySearchSymm (searchFn : CandidateFinder) (tgt : Expr) : MetaM (Array Expr) := do
  let l1 ← librarySearchCore searchFn tgt
  if let some (fn, symm) ← findSymm tgt then
    let l2 ← librarySearchCore searchFn symm
    let l2 ← l2.mapM (mapForallTelescope (fun e => pure (mkApp fn e)))
    pure $ interleave l1 l2
  else
    pure $ l1

/-- A type synonym for our subgoal ranking algorithm. -/
def subgoalRankType : Type := Bool × Nat × Int
  deriving ToString

instance : Ord subgoalRankType :=
  have : Ord (Nat × Int) := lexOrd
  lexOrd

/-- Returns a tuple:
* are there no remaining goals?
* how many local hypotheses were used?
* how many goals remain, negated?

Larger values (i.e. no remaining goals, more local hypotheses, fewer remaining goals)
are better.
-/
def subgoalRanking (goal : MVarId) (subgoals : List MVarId) : MetaM subgoalRankType := do
  return (subgoals.isEmpty, ← countLocalHypsUsed (.mvar goal), - subgoals.length)

/-- Sort the incomplete results from `librarySearchCore` according to
* the number of local hypotheses used (the more the better) and
* the number of remaining subgoals (the fewer the better).
-/
def sortResults (goal : MVarId) (R : Array (List MVarId × MetavarContext)) :
    MetaM (Array (List MVarId × MetavarContext)) := do
  let R' ← R.mapM fun (gs, ctx) => do
    return (← withMCtx ctx (subgoalRanking goal gs), gs, ctx)
  let R'' := R'.qsort fun a b => compare a.1 b.1 = Ordering.gt
  return R''.map (·.2)

/-- Invoke action on candidates until one succeeds by returning no goals. -/
def tryCandidateLemmas (shouldAbort : MetaM Bool)
    (act : MVarId → Expr → MetaM (List MVarId))
    (goal : MVarId)
    (candidates : Array Expr) :
    MetaM (Option (Array (List MVarId × MetavarContext))) := do
  let mut a := #[]
  for c in candidates do
    if ←shouldAbort then
      break
    let s ← saveState
    match ← (tryCatch (.some <$> act goal c) (fun _ => pure none)) with
    | none =>
      restoreState s
      pure ()
    | some remaining =>
      let ctx ← getMCtx
      restoreState s
      if remaining.isEmpty then
        setMCtx ctx
        return none
      let ctx ← getMCtx
      restoreState s
      a := a.push (remaining, ctx)
  return (.some a)

/--
Return an action that returns true when  the remaining heartbeats is less
than the currently remaining heartbeats * leavePercent / 100.
-/
def mkHeartbeatCheck (leavePercent : Nat) : MetaM (MetaM Bool) := do
  let maxHB ← getMaxHeartbeats
  let hbThreshold := (← getRemainingHeartbeats) * leavePercent / 100
  -- Return true if we should stop
  pure $
    if maxHB = 0 then
      pure false
    else do
      return (← getRemainingHeartbeats) < hbThreshold

/-- Shortcut for calling `solveByElim`. -/
def solveByElim (required : List Expr) (exfalso := false) (depth) (goals : List MVarId) := do
  -- There is only a marginal decrease in performance for using the `symm` option for `solveByElim`.
  -- (measured via `lake build && time lake env lean test/librarySearch.lean`).
  let cfg : SolveByElim.Config :=
    { maxDepth := depth, exfalso := exfalso, symm := true, commitIndependentGoals := true }
  let cfg := if !required.isEmpty then cfg.requireUsingAll required else cfg
  let ⟨lemmas, ctx⟩ ← SolveByElim.mkAssumptionSet false false [] [] #[]
  SolveByElim.solveByElim cfg lemmas ctx goals

private def LibSearchState := Option CandidateFinder
  deriving Inhabited

private def mkInitialLibSearch : IO LibSearchState := do
  pure .none

private initialize ext : EnvExtension LibSearchState ←
  registerEnvExtension mkInitialLibSearch

/--
Try to solve the goal either by:
* calling `solveByElim`
* or applying a library lemma then calling `solveByElim` on the resulting goals.

If it successfully closes the goal, returns `none`.
Otherwise, it returns `some a`, where `a : Array (MetavarContext × List MVarId)`,
with an entry for each library lemma which was successfully applied,
containing the metavariable context after the application, and a list of the subsidiary goals.

(Always succeeds, and the metavariable context stored in the monad is reverted,
unless the goal was completely solved.)

(Note that if `solveByElim` solves some but not all subsidiary goals,
this is not currently tracked.)
-/
def librarySearch (goal : MVarId) (required : List Expr)
    (solveByElimDepth := 6) (leavePercentHeartbeats : Nat := 10) :
    MetaM (Option (Array (List MVarId × MetavarContext))) := do

  let importFinder ←
        match ext.getState (←getEnv) with
        | .some f => pure f
        | .none =>
          let f ← defaultCandidateFinder.get
          modifyEnv (ext.setState · (.some f))
          pure f
  let searchFn (ty : Expr) := do
      let localMap ← (← getEnv).constants.map₂.foldlM (init := {}) (DiscrTreeFinder.updateTree {})
      let locals := (← localMap.getMatch  ty {}).reverse
      pure <| locals ++ (←importFinder ty)
  let librarySearchEmoji := fun
    | .error _ => bombEmoji
    | .ok (some _) => crossEmoji
    | .ok none => checkEmoji
  withTraceNode `Tactic.librarySearch (return m!"{librarySearchEmoji ·} {← goal.getType}") do
  profileitM Exception "librarySearch" (← getOptions) do
    let tactic newGoals := solveByElim required (exfalso := false) (depth := solveByElimDepth) newGoals
    let act := librarySearchLemma tactic required.isEmpty
    -- Return true if we should stop
    let shouldAbort ← mkHeartbeatCheck leavePercentHeartbeats
    let candidates ← librarySearchCore searchFn (← goal.getType)
    match ← tryCandidateLemmas shouldAbort act goal candidates with
    | none => pure none
    | some a => pure (some (← sortResults goal a))

open Lean.Parser.Tactic

-- TODO: implement the additional options for `library_search` from Lean 3,
-- in particular including additional lemmas
-- with `exact? [X, Y, Z]` or `exact? with attr`.

-- For now we only implement the basic functionality.
-- The full syntax is recognized, but will produce a "Tactic has not been implemented" error.

/-- Syntax for `std_exact?` -/
syntax (name := std_exact?') "std_exact?" (config)? (simpArgs)? (" using " (colGt ident),+)?
    ("=>" tacticSeq)? : tactic

--/-- Syntax for `std_apply?` -/
--syntax (name := apply?') "std_apply?" (config)? (simpArgs)?
--  (" using " (colGt term),+)? : tactic

open Elab.Tactic Elab Tactic
open Parser.Tactic (tacticSeq)

/-- Implementation of the `exact?` tactic. -/
def exact? (tk : Syntax) (required : Option (Array (TSyntax `term)))
   (_solver : Option (TacticM Info)) (requireClose : Bool) :
    TacticM Unit := do
  let mvar ← getMainGoal
  let (_, goal) ← (← getMainGoal).intros
  goal.withContext do
    let required := (← (required.getD #[]).mapM getFVarId).toList.map .fvar
    if let some suggestions ← librarySearch goal required then
      if requireClose then
        throwError "`exact?` could not close the goal. Try `apply?` to see partial suggestions."
      reportOutOfHeartbeats `library_search tk
      for suggestion in suggestions do
        withMCtx suggestion.2 do
          addExactSuggestion tk (← instantiateMVars (mkMVar mvar)).headBeta (addSubgoalsMsg := true)
      if suggestions.isEmpty then logError "apply? didn't find any relevant lemmas"
      admitGoal goal
    else
      addExactSuggestion tk (← instantiateMVars (mkMVar mvar)).headBeta

elab_rules : tactic
  | `(tactic| std_exact? $[using $[$required],*]? $[=> $solver]?) => do
  let solver ← match solver with
                | none => pure none
                | some t => some <$> mkInitialTacticInfo t
  exact? (← getRef) required solver true

--elab_rules : tactic | `(tactic| std_apply? $[using $[$required],*]?) => do
--  exact? (← getRef) required false

--/-- Deprecation warning for `library_search`. -/
--elab tk:"library_search" : tactic => do
--  logWarning ("`library_search` has been renamed to `apply?`" ++
--    " (or `exact?` if you only want solutions closing the goal)")
--  exact? tk none false

open Elab Term in
/-- Term elaborator using the `exact?` tactic. -/
elab tk:"exact?%" : term <= expectedType => do
  let goal ← mkFreshExprMVar expectedType
  let (_, introdGoal) ← goal.mvarId!.intros
  introdGoal.withContext do
    if let some suggestions ← librarySearch introdGoal [] then
      reportOutOfHeartbeats `library_search tk
      for suggestion in suggestions do
        withMCtx suggestion.2 do
          addTermSuggestion tk (← instantiateMVars goal).headBeta
      if suggestions.isEmpty then logError "exact? didn't find any relevant lemmas"
      mkSorry expectedType (synthetic := true)
    else
      addTermSuggestion tk (← instantiateMVars goal).headBeta
      instantiateMVars goal

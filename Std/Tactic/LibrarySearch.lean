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

open LazyDiscrTree (Key LazyEntry PreDiscrTree)

private def libSearchContext : Meta.Context := {
    config := { transparency := .reducible }
  }

private def pushEntry (r : IO.Ref (PreDiscrTree α)) (lctx : LocalContext × LocalInstances)
    (type : Expr) (v : α) : MetaM Unit := do
  let (k, todo) ← LazyDiscrTree.rootKey {} type
  r.modify (·.push k (todo, lctx, v))

/-- Information about a failed import. -/
private structure ImportFailure where
  /-- Module with constant that import failed on. -/
  module  : Name
  /-- Constant that import failed on. -/
  const   : Name
  /-- Exception that triggers error. -/
  exception : Exception

/--
Contains the pre discrimination tree and any errors occuring during initialization of
the library search tree.
-/
private structure InitResults (α : Type) where
  tree  : PreDiscrTree α := {}
  errors : Array ImportFailure := #[]

instance : Inhabited (InitResults α) where
  default := {}

namespace InitResults

/-- Combine two error collections. -/
protected def append (x y : InitResults α) : InitResults α :=
  let { tree := xv, errors := xe } := x
  let { tree := yv, errors := ye } := y
  { tree := xv ++ yv, errors := xe ++ ye }

instance : Append (InitResults α) where
  append := InitResults.append

end InitResults

/-- Information generation from imported modules. -/
private structure ImportData where
  cache : IO.Ref (Lean.Meta.Cache)
  data : IO.Ref (PreDiscrTree (Name × DeclMod))
  errors : IO.Ref (Array ImportFailure)

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
          let (k, todo) ← LazyDiscrTree.rootKey {} type
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
  | .error e =>
    let i : ImportFailure := {
      module := modName,
      const := name,
      exception := e
    }
    d.errors.modify (·.push i)

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
    BaseIO (InitResults (Name × DeclMod)) := do
  let dm ← d.data.swap {}
  let de ← d.errors.swap #[]
  pure ⟨dm, de⟩

private def createImportedEnvironmentSeq (env : Environment) (start stop : Nat) :
    BaseIO (InitResults (Name × DeclMod)) :=
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

The value below was picked because it roughly correponded to 50ms of work on the machine this was
developed on.  Smaller numbers did not seem to improve performance when importing Std and larger
numbers (<10k) seemed to degrade initialization performance.
-/
private def constantsPerTask : Nat := 6500

/-- Get the rests of each task and merge using combining function -/
private def combineGet [Append α] (z : α) (tasks : Array (Task α)) : α :=
  tasks.foldl (fun x t => x ++ t.get) (init := z)

private def createImportedEnvironment (opts : Options) (env : Environment) :
    BaseIO (LazyDiscrTree (Name × DeclMod)) := profileitIO "librarySearch launch" opts $ do
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
  let tasks ← go #[] 0 0 0
  pure <| (combineGet default tasks).tree.toLazy
  termination_by go _ idx => env.header.moduleData.size - idx

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
A library search candidate using symmetry includes the goal to solve, the metavar
context for that goal, and the name and orientation of a rule to try using with goal.
-/
@[reducible]
def Candidate :=  (MVarId × MetavarContext) × (Name × DeclMod)

/--
Try applying the given lemma (with symmetry modifier) to the goal,
then try to close subsequent goals using `solveByElim`.
If `solveByElim` succeeds, we return `[]` as the list of new subgoals,
otherwise the full list of subgoals.
-/
def librarySearchLemma (act : List MVarId → MetaM (List MVarId)) (allowFailure : Bool)
    (cand : Candidate) : MetaM (List MVarId) := do
  let ((goal, mctx), (name, mod)) := cand
  withTraceNode `Tactic.stdLibrarySearch (return m!"{emoji ·} trying {name} with {mod} ") do
    setMCtx mctx
    let lem ← mkLibrarySearchLemma name mod
    let newGoals ← goal.apply lem { allowSynthFailures := true }
    try
      act newGoals
    catch _ =>
      if allowFailure then
        pure newGoals
      else
        failure

/--
Interleave x y interleaves the elements of x and y until one is empty and then returns
final elements in other list.
-/
def interleaveWith {α β γ} (f : α → γ) (x : Array α) (g : β → γ) (y : Array β) : Array γ :=
    Id.run do
  let mut res := Array.mkEmpty (x.size + y.size)
  let n := min x.size y.size
  for h : i in [0:n] do
    have p : i < min x.size y.size := h.2
    have q : i < x.size := Nat.le_trans p (Nat.min_le_left ..)
    have r : i < y.size := Nat.le_trans p (Nat.min_le_right ..)
    res := res.push (f x[i])
    res := res.push (g y[i])
  let last :=
        if x.size > n then
          (x.extract n x.size).map f
        else
          (y.extract n y.size).map g
  pure $ res ++ last

/--
Run `searchFn` on both the goal and `symm` applied to the goal.
-/
def librarySearchSymm (searchFn : CandidateFinder) (goal : MVarId) : MetaM (Array Candidate) := do
  let tgt ← goal.getType
  let l1 ← searchFn tgt
  let coreMCtx ← getMCtx
  let coreGoalCtx := (goal, coreMCtx)
  if let some symmGoal ← observing? goal.applySymm then
    let newType ← instantiateMVars  (← symmGoal.getType)
    let l2 ← searchFn newType
    let symmMCtx ← getMCtx
    let symmGoalCtx := (symmGoal, symmMCtx)
    setMCtx coreMCtx
    pure $ interleaveWith (coreGoalCtx, ·) l1 (symmGoalCtx, ·) l2
  else
    pure $ l1.map (coreGoalCtx, ·)

/-- A type synonym for our subgoal ranking algorithm. -/
def SubgoalRankType := Bool × Nat × Int
  deriving ToString

instance : Ord SubgoalRankType :=
  have : Ord (Nat × Int) := lexOrd
  lexOrd

/-- Count how many local hypotheses appear in an expression. -/
def countLocalHypsUsed [Monad m] [MonadLCtx m] [MonadMCtx m] (e : Expr) : m Nat := do
  let e' ← instantiateMVars e
  return (← getLocalHyps).foldr (init := 0) fun h n => if h.occurs e' then n + 1 else n

/-- Returns a tuple:
* are there no remaining goals?
* how many local hypotheses were used?
* how many goals remain, negated?

Larger values (i.e. no remaining goals, more local hypotheses, fewer remaining goals)
are better.
-/
def subgoalRanking (goal : MVarId) (subgoals : List MVarId) : MetaM SubgoalRankType := do
  return (subgoals.isEmpty, ← countLocalHypsUsed (.mvar goal), - subgoals.length)

/-- Sort the incomplete results from `librarySearchSymm` according to
* the number of local hypotheses used (the more the better) and
* the number of remaining subgoals (the fewer the better).
-/
def sortResults (goal : MVarId) (R : Array (List MVarId × MetavarContext)) :
    MetaM (Array (List MVarId × MetavarContext)) := do
  let R' ← R.mapM fun (gs, ctx) => do
    return (← withMCtx ctx (subgoalRanking goal gs), gs, ctx)
  let R'' := R'.qsort fun a b => compare a.1 b.1 = Ordering.gt
  return R''.map (·.2)

/--
An exception Id that indicates further speculation on candidate lemmas should stop
and current results returned.
-/
private initialize abortSpeculationId : InternalExceptionId ←
  registerInternalExceptionId `Std.Tactic.LibrarySearch.abortSpeculation

/--
Called to abort speculative execution in library search.
-/
def abortSpeculation [MonadExcept Exception m] : m α :=
  throw (Exception.internal abortSpeculationId {})

/-- Returns true if this is an abort speculation exception. -/
def isAbortSpeculation : Exception → Bool
| .internal id _ => id == abortSpeculationId
| _ => false

/--
Sequentially invokes a tactic `act` on each value in candidates on the current state.

The tactic `act` should return a list of meta-variables that still need to be resolved.
If this list is empty, then no variables remain to be solved, and `tryOnEach` returns
`none` with the environment set so each goal is resolved.

If the action throws an internal exception with the `abortSpeculationId` id then
further computation is stoped and intermediate results returned. If any other
exception is thrown, then it is silently discarded.
-/
def tryOnEach
    (act : Candidate → MetaM (List MVarId))
    (candidates : Array Candidate) :
    MetaM (Option (Array (List MVarId × MetavarContext))) := do
  let mut a := #[]
  let s ← saveState
  for c in candidates do
    match ← (tryCatch (Except.ok <$> act c) (pure ∘ Except.error)) with
    | .error e =>
      restoreState s
      if isAbortSpeculation e then
        break
    | .ok remaining =>
      if remaining.isEmpty then
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
def solveByElim (required : List Expr) (exfalso : Bool) (goals : List MVarId) (maxDepth : Nat) := do
  -- There is only a marginal decrease in performance for using the `symm` option for `solveByElim`.
  -- (measured via `lake build && time lake env lean test/librarySearch.lean`).
  let cfg : SolveByElim.Config :=
    { maxDepth, exfalso := exfalso, symm := true, commitIndependentGoals := true }
  let ⟨lemmas, ctx⟩ ← SolveByElim.mkAssumptionSet false false [] [] #[]
  let cfg := if !required.isEmpty then cfg.requireUsingAll required else cfg
  SolveByElim.solveByElim cfg lemmas ctx goals

/-- State for resolving imports -/
private def LibSearchState := IO.Ref (Option CandidateFinder)

private initialize LibSearchState.default : IO.Ref (Option CandidateFinder) ← do
  IO.mkRef .none

private instance : Inhabited LibSearchState where
  default := LibSearchState.default

private initialize ext : EnvExtension LibSearchState ←
  registerEnvExtension (IO.mkRef .none)

private def librarySearchEmoji : Except ε (Option α) → String
| .error _ => bombEmoji
| .ok (some _) => crossEmoji
| .ok none => checkEmoji

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
def librarySearch (goal : MVarId)
    (tactic : Bool → List MVarId → MetaM (List MVarId))
    (allowFailure : Bool := true)
    (leavePercentHeartbeats : Nat := 10) :
    MetaM (Option (Array (List MVarId × MetavarContext))) := do
  let importFinder ← do
        let r := ext.getState (←getEnv)
        match ←r.get with
        | .some f => pure f
        | .none =>
          let f ← defaultCandidateFinder.get
          r.set (.some f)
          pure f
  let searchFn (ty : Expr) := do
      let localMap ← (← getEnv).constants.map₂.foldlM (init := {}) (DiscrTreeFinder.updateTree {})
      let locals := (← localMap.getMatch  ty {}).reverse
      pure <| locals ++ (← importFinder ty)
  withTraceNode `Tactic.stdLibrarySearch (return m!"{librarySearchEmoji ·} {← goal.getType}") do
  profileitM Exception "librarySearch" (← getOptions) do
  (do
    _ ← tactic true [goal]
    return none)  <|>
  (do
    -- Create predicate that returns true when running low on heartbeats.
    let shouldAbort ← mkHeartbeatCheck leavePercentHeartbeats
    let candidates ← librarySearchSymm searchFn goal
    let act := fun cand => do
        if ←shouldAbort then
          abortSpeculation
        librarySearchLemma (tactic false) allowFailure cand
    match ← tryOnEach act candidates with
    | none => pure none
    | some a => pure (some (← sortResults goal a)))

open Lean.Parser.Tactic

-- TODO: implement the additional options for `library_search` from Lean 3,
-- in particular including additional lemmas
-- with `exact? [X, Y, Z]` or `exact? with attr`.

-- For now we only implement the basic functionality.
-- The full syntax is recognized, but will produce a "Tactic has not been implemented" error.

/-- Syntax for `std_exact?` -/
syntax (name := std_exact?') "std_exact?" (config)? (simpArgs)? (" using " (colGt ident),+)?
    ("=>" tacticSeq)? : tactic

/-- Syntax for `std_apply?` -/
syntax (name := std_apply?') "std_apply?" (config)? (simpArgs)? (" using " (colGt term),+)? : tactic

open Elab.Tactic Elab Tactic
open Parser.Tactic (tacticSeq)

/-- Implementation of the `exact?` tactic. -/
def exact? (tk : Syntax) (required : Option (Array (TSyntax `term)))
   (solver : Option (TSyntax `Lean.Parser.Tactic.tacticSeq)) (requireClose : Bool) :
    TacticM Unit := do
  let mvar ← getMainGoal
  let (_, goal) ← (← getMainGoal).intros
  goal.withContext do
    let required := (← (required.getD #[]).mapM getFVarId).toList.map .fvar
    let tactic ←
      match solver with
      | none =>
        pure (fun g => solveByElim required g (maxDepth := 6))
      | some t =>
        let _ <- mkInitialTacticInfo t
        throwError "Do not yet support custom exact?/apply? tactics."
    match ← librarySearch goal tactic (allowFailure := required.isEmpty) with
    -- Found goal that closed problem
    | none =>
      addExactSuggestion tk (← instantiateMVars (mkMVar mvar)).headBeta
    -- Found suggestions
    | some suggestions =>
      if requireClose then
        throwError "`exact?` could not close the goal. Try `apply?` to see partial suggestions."
      reportOutOfHeartbeats `library_search tk
      for (_, suggestionMCtx) in suggestions do
        withMCtx suggestionMCtx do
          addExactSuggestion tk (← instantiateMVars (mkMVar mvar)).headBeta (addSubgoalsMsg := true)
      if suggestions.isEmpty then logError "apply? didn't find any relevant lemmas"
      admitGoal goal

elab_rules : tactic
  | `(tactic| std_exact? $[using $[$lemmas],*]? $[=> $solver]?) => do
  exact? (← getRef) lemmas solver true

elab_rules : tactic | `(tactic| std_apply? $[using $[$required],*]?) => do
  exact? (← getRef) required none false

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
    let tactic := fun exfalso g => solveByElim []  (maxDepth := 6) exfalso g
    if let some suggestions ← librarySearch introdGoal tactic then
      reportOutOfHeartbeats `library_search tk
      for suggestion in suggestions do
        withMCtx suggestion.2 do
          addTermSuggestion tk (← instantiateMVars goal).headBeta
      if suggestions.isEmpty then logError "exact? didn't find any relevant lemmas"
      mkSorry expectedType (synthetic := true)
    else
      addTermSuggestion tk (← instantiateMVars goal).headBeta
      instantiateMVars goal

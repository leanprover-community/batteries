/-
Copyright (c) 2021-2023 Gabriel Ebner and Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner, Joe Hendrix, Scott Morrison
-/
import Lean.Meta.Tactic.TryThis
import Std.Lean.CoreM
import Std.Lean.Expr
import Std.Lean.Meta.DiscrTree
import Std.Lean.Meta.LazyDiscrTree
import Std.Lean.Parser
import Std.Data.Option.Basic
import Std.Tactic.SolveByElim
import Std.Util.Pickle

/-!
# Library search

This file defines tactics `std_exact?` and `std_apply?`,
(formerly known as `library_search`)
and a term elaborator `std_exact?%`
that tries to find a lemma
solving the current goal
(subgoals are solved using `solveByElim`).

```
example : x < x + 1 := std_exact?%
example : Nat := by std_exact?
```

These functions will likely lose their `std_` prefix once
we are ready to replace the corresponding implementations in Mathlib.
-/

namespace Std.Tactic.LibrarySearch

open Lean Meta Tactic.TryThis

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

open LazyDiscrTree (InitEntry isBlackListed createImportedEnvironment)

namespace DiscrTreeFinder

open System (FilePath)


/--
Once we reach Mathlib, and have `cache` available,
we may still want to load a precomputed cache for `exact?` from a `.olean` file.

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
  pure <| tree.insertCore k v

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


/--
The maximum number of constants an individual task performed.

The value below was picked because it roughly correponded to 50ms of work on the machine this was
developed on.  Smaller numbers did not seem to improve performance when importing Std and larger
numbers (<10k) seemed to degrade initialization performance.
-/
private def constantsPerTask : Nat := 6500

private def addImport (name : Name) (constInfo : ConstantInfo) :
    MetaM (Array (InitEntry (Name × DeclMod))) :=
  forallTelescope constInfo.type fun _ type => do
    let e ← InitEntry.fromExpr type (name, DeclMod.none)
    let a := #[e]
    if e.key == .const ``Iff 2 then
      let a := a.push (←e.mkSubEntry 0 (name, DeclMod.mp))
      let a := a.push (←e.mkSubEntry 1 (name, DeclMod.mpr))
      pure a
    else
      pure a

/--
Candidate finding function that uses strict discrimination tree for resolution.
-/
def mkImportFinder : IO CandidateFinder := do
  let ref ← IO.mkRef none
  pure fun ty => do
    let importTree ← (←ref.get).getDM $ do
      profileitM Exception  "librarySearch launch" (←getOptions) $
        createImportedEnvironment (←getEnv) (constantsPerTask := constantsPerTask) addImport
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
The preferred candidate finding function.
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
private def librarySearchLemma (cfg : ApplyConfig) (act : List MVarId → MetaM (List MVarId))
    (allowFailure : MVarId → MetaM Bool) (cand : Candidate)  : MetaM (List MVarId) := do
  let ((goal, mctx), (name, mod)) := cand
  withTraceNode `Tactic.stdLibrarySearch (return m!"{emoji ·} trying {name} with {mod} ") do
    setMCtx mctx
    let lem ← mkLibrarySearchLemma name mod
    let newGoals ← goal.apply lem cfg
    try
      act newGoals
    catch _ =>
      if ← allowFailure goal then
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
further computation is stopped and intermediate results returned. If any other
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
    { maxDepth, exfalso := exfalso, symm := true, commitIndependentGoals := true,
      transparency := ← getTransparency,
      -- `constructor` has been observed to significantly slow down `exact?` in Mathlib.
      constructor := false }
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

private def librarySearch' (goal : MVarId)
    (tactic : List MVarId → MetaM (List MVarId))
    (allowFailure : MVarId → MetaM Bool)
    (leavePercentHeartbeats : Nat) :
    MetaM (Option (Array (List MVarId × MetavarContext))) := do
  withTraceNode `Tactic.stdLibrarySearch (return m!"{librarySearchEmoji ·} {← goal.getType}") do
  profileitM Exception "librarySearch" (← getOptions) do
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
  -- Create predicate that returns true when running low on heartbeats.
  let shouldAbort ← mkHeartbeatCheck leavePercentHeartbeats
  let candidates ← librarySearchSymm searchFn goal
  let cfg : ApplyConfig := { allowSynthFailures := true }
  let act := fun cand => do
      if ←shouldAbort then
        abortSpeculation
      librarySearchLemma cfg tactic allowFailure cand
  tryOnEach act candidates

/--
Try to solve the goal either by:
* calling `tactic true`
* or applying a library lemma then calling `tactic false` on the resulting goals.

Typically here `tactic` is `solveByElim`,
with the `Bool` flag indicating whether it may retry with `exfalso`.

If it successfully closes the goal, returns `none`.
Otherwise, it returns `some a`, where `a : Array (List MVarId × MetavarContext)`,
with an entry for each library lemma which was successfully applied,
containing a list of the subsidiary goals, and the metavariable context after the application.

(Always succeeds, and the metavariable context stored in the monad is reverted,
unless the goal was completely solved.)

(Note that if `solveByElim` solves some but not all subsidiary goals,
this is not currently tracked.)
-/
def librarySearch (goal : MVarId)
    (tactic : Bool → List MVarId → MetaM (List MVarId))
    (allowFailure : MVarId → MetaM Bool := fun _ => pure true)
    (leavePercentHeartbeats : Nat := 10) :
    MetaM (Option (Array (List MVarId × MetavarContext))) := do
  (tactic true [goal] *> pure none) <|>
  librarySearch' goal (tactic false) allowFailure leavePercentHeartbeats

open Lean.Parser.Tactic

-- TODO: implement the additional options for `library_search` from Lean 3,
-- in particular including additional lemmas
-- with `std_exact? [X, Y, Z]` or `std_exact? with attr`.

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
        pure (fun exfalso => solveByElim required (exfalso := exfalso) (maxDepth := 6))
      | some t =>
        let _ <- mkInitialTacticInfo t
        throwError "Do not yet support custom std_exact?/std_apply? tactics."
    let allowFailure := fun g => do
      let g ← g.withContext (instantiateMVars (.mvar g))
      return required.all fun e => e.occurs g
    match ← librarySearch goal tactic allowFailure with
    -- Found goal that closed problem
    | none =>
      addExactSuggestion tk (← instantiateMVars (mkMVar mvar)).headBeta
    -- Found suggestions
    | some suggestions =>
      if requireClose then throwError
        "`std_exact?` could not close the goal. Try `std_apply?` to see partial suggestions."
      reportOutOfHeartbeats `library_search tk
      for (_, suggestionMCtx) in suggestions do
        withMCtx suggestionMCtx do
          addExactSuggestion tk (← instantiateMVars (mkMVar mvar)).headBeta (addSubgoalsMsg := true)
      if suggestions.isEmpty then logError "std_apply? didn't find any relevant lemmas"
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
elab tk:"std_exact?%" : term <= expectedType => do
  let goal ← mkFreshExprMVar expectedType
  let (_, introdGoal) ← goal.mvarId!.intros
  introdGoal.withContext do
    let tactic := fun exfalso g => solveByElim []  (maxDepth := 6) exfalso g
    if let some suggestions ← librarySearch introdGoal tactic then
      reportOutOfHeartbeats `library_search tk
      for suggestion in suggestions do
        withMCtx suggestion.2 do
          addTermSuggestion tk (← instantiateMVars goal).headBeta
      if suggestions.isEmpty then logError "std_exact? didn't find any relevant lemmas"
      mkSorry expectedType (synthetic := true)
    else
      addTermSuggestion tk (← instantiateMVars goal).headBeta
      instantiateMVars goal

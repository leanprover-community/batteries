module

public meta import Batteries.CodeAction.Misc
public meta import Batteries.Data.List

@[expose] public meta section

namespace Batteries.CodeAction

open Lean Meta Elab Server RequestM CodeAction


/-- Filter for the info-nodes to find the match-nodes. -/
def isMatchTerm : Info → Bool
  | .ofTermInfo i => i.stx.isOfKind ``Lean.Parser.Term.match
  | _ => false

/-- Returns the String.range that encompasses `match e (with)`. -/
def getMatchHeaderRange? (matchStx : Syntax) : Option Lean.Syntax.Range := do
  match matchStx with
  | `(term| match
    $[(generalizing := $generalizingVal)]?
    $[(motive := $motiveVal)]?
    $[$discrs:matchDiscr],*
    with $_) => --Here the $alts would go, if they were already typed. Else $_  will match "missing"

    -- Isolate the syntax of only the "match" atom to get the starting position:
    let mStx ← matchStx.getArgs.find? (fun s => s.isAtom && s.getAtomVal == "match")
    let startPos ← mStx.getPos? -- begin of 'match' keyword

    -- Depending on the existence of 'with', return the correct range:
    if let some withStx := (matchStx.getArgs.find? (fun s => s.isAtom && s.getAtomVal == "with"))
      then return ⟨startPos, ←withStx.getTailPos?⟩
    else
      let lastMatchDiscr ← discrs.back?
      return ⟨startPos, ←lastMatchDiscr.raw.getTailPos?⟩
  | _ => none

/-- Flattens an Infotree into an array of Info-nodes that fulfill p. -/
partial def findAllInfos (p : Info → Bool) (t : InfoTree) : Array Info :=
  loop t #[]
where
  /-- Inner loop for `findAllInfos`. -/
  loop (t : InfoTree) (acc : Array Info) : Array Info :=
    match t with
    | .context _ childTree => loop childTree acc
    | .node info children  =>
      let acc' := if p info then acc.push info else acc
      children.foldl (fun currentAcc child => loop child currentAcc) acc'
    | .hole _              => acc

/-- Computes for a constructor, if it makes sense to use `@constr` in a match, by determining
    if it has any non-parameter implicit arguments. -/
def hasImplicitNonparArg (ctor : Name) (env : Environment) : Bool := Id.run do
    let some (.ctorInfo ctorInfo) := env.find? ctor | panic! "bad inductive"
    let explicitArgs := getExplicitArgs ctorInfo.type #[]
    let allArgs := getAllArgs ctorInfo.type #[]
    let some (.inductInfo indInfo) := env.find? ctorInfo.induct | panic! "not an inductive"
    let numParams := indInfo.numParams
    return (allArgs.size - (explicitArgs.size + numParams) > 0)

/-- From a constructor-name e.g. `Option.some` construct the corresponding match pattern, e.g.
    `.some val`. We implement special cases for `Nat` and `List`, `Option` and `Bool` to e.g.
    produce `n + 1` instead of `Nat.succ n`. -/
def pattern_from_constructor (ctor : Name) (env : Environment) (suffix : String)
    (explicitArgsOnly : Bool) (ctor_hasImplicitNonparArg : Bool): Option String := do
  let some (.ctorInfo ctorInfo) := env.find? ctor | panic! "bad inductive"
  let some (.inductInfo indInfo) := env.find? ctorInfo.induct | panic! "not an inductive"
  let numParams := indInfo.numParams
  let ctor_short := toString (ctor.updatePrefix .anonymous)
  let some namePrefix := indInfo.name.components.getLast? | panic "Not able to determine name of inductive"
  let ctor_long := s!"{toString namePrefix}.{ctor_short}"
  let explicitCtorArgs := getExplicitArgs ctorInfo.type #[]
  let allCtorArgs := getAllArgs ctorInfo.type #[]

  /- Special cases with nicer Notation. None of these constructors has any implicit arguments
     that aren't parameters, i.e. that aren't already determined by the match discriminant.
     So it doesn't make sense to use them with `@`. That's why we *always* nicely print them
     regardless of the setting `explicitArgsOnly`. -/
  match ctor with
  | (.str (.str .anonymous "Nat") "zero") => "0"
  /- At the moment this evaluates to "n + 1": -/
  | (.str (.str .anonymous "Nat") "succ") => s!"{explicitCtorArgs[0]!}{suffix} + 1" --
  | (.str (.str .anonymous "List") "nil") => "[]"
  /- At the moment this evaluates to "head :: tail": -/
  | (.str (.str .anonymous "List") "cons") =>
    s!"{explicitCtorArgs[0]!}{suffix} :: {explicitCtorArgs[1]!}{suffix}"
  | (.str (.str .anonymous "Option") "some") => s!"some {explicitCtorArgs[0]!}{suffix}"
  | (.str (.str .anonymous "Option") "none") => "none"
  | (.str (.str .anonymous "Bool") "true") => "true"
  | (.str (.str .anonymous "Bool") "false") => "false"
  | _ =>
    /- This is the Default case. It fills the constructor arguments with the variable names `arg` which were
       used in the inductive type specification. When using this action with multiple (same-type)
       arguments these might clash, so we fix it by appending a suffix like `_2` - you will
       probably want to rename these suffixed names yourself.
       If the the user wants the match to contain the implicit arguments as well, we
       additionally put `_` for every `parameter` (a parameter is an argument to the inductive
       type that is fixed over constructors), since these should already be determined by the
       match discriminant. One could elaborate the type of this discriminant and fill the parameters
       from there, but we don't see any value in this. -/
      -- totalArgs - explicitargs - parameters
    if explicitArgsOnly || Bool.not ctor_hasImplicitNonparArg then
      let mut str := s!".{ctor_short}"
      for arg in explicitCtorArgs do
        str := str ++ if arg.hasNum || arg.isInternal then " _" else s!" {arg}{suffix}"
      return str
    else
      let mut str := s!"@{ctor_long}"
      for i in [:allCtorArgs.size] do
        let arg := allCtorArgs[i]!
        str := str ++
          if i < numParams || arg.hasNum || arg.isInternal then
            " _"
          else
            s!" {arg}{suffix}"
      return str


/--
Invoking tactic code action `Generate a list of alternatives for this match.` in the
following:
```lean
def myfun2 (n : Nat) : Nat :=
  match n
```
produces:
```lean
def myfun2 (n : Nat) : Nat :=
  match n with
  | 0 => _
  | n + 1 => _
```
Also has support for multiple discriminants, e.g.
```
def myfun3 (o : Option Bool) (m : Nat) : Nat :=
  match o, m with
```
can be expanded into
```
def myfun3 (o : Option Bool) (m : Nat) : Nat :=
  match o, m with
  | none, 0 => _
  | none, n_2 + 1 => _
  | some val_1, 0 => _
  | some val_1, n_2 + 1 => _
```
If it makes sense to use at least one of the constructors with `@` (i.e. iff it has an
implicit non-parameter argument) then we also show a codeaction that expands every such constructor
with `@`. E.g. invoking `Generate a list of equations with implicit arguments for this match.` in
the following
```
inductive TermWithImplicit (F : Nat → Type u) (α : Type w)
  | var (x : α) : TermWithImplicit F α
  | func {l : Nat} (f : F l) (ts : Fin l → TermWithImplicit F α) : TermWithImplicit F α

def myfun4 (t : TermWithImplicit F α) : Nat := by
  match t with
```
produces
```
def myfun4 (t : TermWithImplicit F α) : Nat := by
  match t with
  | .var x => _
  | @TermWithImplicit.func _ _ l f ts => _
```
where the implicit argument `{l : Nat}` is now usable.
Note that the arguments `F` and `α` were filled with `_` since they are `parameters`
(a parameter is an argument to an inductive type that is fixed over constructors), i.e.
they are already determined by the match discriminant `t`. We dont explicitly fill them,
since they are rarely used in a match.
-/
@[command_code_action]
def matchExpand : CommandCodeAction := fun CodeActionParams snap ctx node => do
  /- Since `match` is a term (not a command) `@[command_code_action Parser.Term.match]` will
  not fire. So we filter `command_code_action` ourselves in Step 1 for now. -/

  /- 1. Find ALL ofTermInfo Info nodes that are of kind `Term.match` -/
  let allMatchInfos := findAllInfos isMatchTerm node

  /- 2. Filter these candidates within the `RequestM` monad based on the cursor being in the
  header lines of these matches. -/
  let doc ← readDoc
  let relevantMatchInfos ← allMatchInfos.filterM fun matchInfo => do
    let some headerRangeRaw := getMatchHeaderRange? matchInfo.stx | return false
    let headerRangeLsp := doc.meta.text.utf8RangeToLspRange headerRangeRaw

    let cursorRangeLsp := CodeActionParams.range
    -- check if the cursor range is contained in the header range
    return (cursorRangeLsp.start ≥ headerRangeLsp.start && cursorRangeLsp.end ≤ headerRangeLsp.end)

  /- 3. Pick the first (and mostly only) candidate. There might sometimes be more,
  since some things are just contained multiple times in 'node'. -/
  let some matchInfo := relevantMatchInfos[0]? | return #[]
  let some headerRangeRaw := getMatchHeaderRange? matchInfo.stx | return #[]

  /- Isolate the array of match-discriminants -/
  let discrs ← match matchInfo.stx with
  | `(term| match
    $[(generalizing := $generalizingVal)]?
    $[(motive := $motiveVal)]?
    $[$discrs:matchDiscr],*
    with $_) => pure discrs
  | _ => return #[]

  /- Reduce discrs to the array of match-discriminants-terms (i.e. "[n1, n2]" in "match n2,n2"). -/
  let some discrTerms := discrs.mapM (fun discr =>
    match discr with
    | `(matchDiscr| $t: term) => some t
    | `(matchDiscr| $_:ident : $t: term) => some t
    | _ => none
    ) | return #[]

  -- Get a Bool, that tells us if "with" is already typed in:
  let withPresent :=
    (matchInfo.stx.getArgs.find? (fun s => s.isAtom && s.getAtomVal == "with")).isSome

  /- Construct a list containing for each discriminant its list of constructor names paired with
     a Bool that determines if it makes sense to use the constructor with `@`.
     The list contains the first discriminant constructors last,
     since we are prepending in the loop. -/
  let mut constructors_rev : List (List (Name × Bool)) := []
  for discrTerm in discrTerms do
    let some (info : TermInfo) := findTermInfo? node discrTerm | return #[]
    let ty ← info.runMetaM ctx (Lean.Meta.inferType info.expr)
    let .const name _ := (← info.runMetaM ctx (whnf ty)).getAppFn | return #[]
    -- Find the inductive constructors of e:
    let some (.inductInfo indInfo) := snap.env.find? name | return #[]
    let ctors := indInfo.ctors
    constructors_rev :=
      (ctors.map (fun ctor ↦ (ctor, hasImplicitNonparArg ctor snap.env)))
        :: constructors_rev

  let mkAction (title : String) (explicitArgsOnly : Bool) : LazyCodeAction :=
      let eager : Lsp.CodeAction := {
      title := title
      kind? := "quickfix"
      }
    { --rest is lightly adapted from eqnStub:
    eager
    lazy? := some do
      let holePos := headerRangeRaw.stop --where we start inserting
      let (indent, _) := findIndentAndIsStart doc.meta.text.source headerRangeRaw.start
      let mut str := if withPresent then "" else " with"

      let indent := "\n".pushn ' ' (indent) --use the same indent as the 'match' line.
      let constructor_combinations := constructors_rev.sections.map List.reverse
      for l in constructor_combinations do
        str := str ++ indent ++ "| "
        for ctor_idx in [:l.length] do
          let (ctor, existsExplicitNonparArg) := l[ctor_idx]!
          let suffix := if constructors_rev.length ≥ 2 then s!"_{ctor_idx + 1}" else ""
          let some pat :=
            pattern_from_constructor ctor snap.env suffix explicitArgsOnly existsExplicitNonparArg |
              panic! "bad inductive"
          str := str ++ pat
          if ctor_idx < l.length - 1 then
            str := str ++ ", "
        str := str ++ s!" => _"
      pure { eager with
        edit? := some <|.ofTextEdit doc.versionedIdentifier {
          range := doc.meta.text.utf8RangeToLspRange ⟨holePos, holePos⟩-- adapted to insert-only
          newText := str
        }
      }
  }
  /- Show the code action with implicit arguments if at least one constructor has an implicit
     non-parameter argument. -/
  let showExplicitCodeAction := constructors_rev.any (fun l ↦
    l.any (fun (_, ctor_hasImplicitNonparArg) ↦ ctor_hasImplicitNonparArg))

  if (showExplicitCodeAction) then
    return #[mkAction "Generate a list of equations for this match." True,
             mkAction "Generate a list of equations with implicit arguments for this match." False]
  else
    return #[mkAction "Generate a list of equations for this match." True]

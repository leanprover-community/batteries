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
def getMatchHeaderRange? (matchStx : Syntax) : Option String.Range := do
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

/-- From a constructor-name e.g. 'Option.some' construct the corresponding match pattern, e.g.
'.some val'. We implement special cases for Nat and List, Option and Bool to e.g.
produce 'n + 1' instead of 'Nat.succ n'.
-/
def pattern_from_constructor (ctor : Name) (env : Environment) (suffix : String)
    : Option String := do
  let some (.ctorInfo ci) := env.find? ctor | panic! "bad inductive"
  let ctor_short := toString (ctor.updatePrefix .anonymous)
  let mut str := ""
  let explicit_args := getExplicitArgs ci.type #[]
  match ctor with
  | (.str (.str .anonymous "Nat") "zero") => "0"
  /- At the moment this evaluates to "n + 1": -/
  | (.str (.str .anonymous "Nat") "succ") => s!"{explicit_args[0]!}{suffix} + 1" --
  | (.str (.str .anonymous "List") "nil") => "[]"
  /- At the moment this evaluates to "head :: tail": -/
  | (.str (.str .anonymous "List") "cons") =>
    s!"{explicit_args[0]!}{suffix} :: {explicit_args[1]!}{suffix}"
  | (.str (.str .anonymous "Option") "some") => s!"some {explicit_args[0]!}{suffix}"
  | (.str (.str .anonymous "Option") "none") => "none"
  | (.str (.str .anonymous "Bool") "true") => "true"
  | (.str (.str .anonymous "Bool") "false") => "false"
  /- Default case: -/
  | _ =>
    str := str ++ s!".{ctor_short}"
    for arg in explicit_args do
      /- This takes the variable names `arg` which were used in the
      inductive type specification. When using this action with multiple (same-type)
      arguments these might clash, so we fix it by appending a suffix like `_2` -
      you will probably want to rename these suffixed names yourself. -/
      str := str ++ if arg.hasNum || arg.isInternal then " _" else s!" {arg}{suffix}"
    return str

/--
Invoking tactic code action "Generate a list of alternatives for this match." in the
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

  /- Construct a list containing for each discriminant its list of constructor names.
  The list contains the first discriminant constructors last, since we are prepending in the loop.-/
  let mut constructors_rev : List (List Name) := []
  for discrTerm in discrTerms do
    let some (info : TermInfo) := findTermInfo? node discrTerm | return #[]
    let ty ← info.runMetaM ctx (Lean.Meta.inferType info.expr)
    let .const name _ := (← info.runMetaM ctx (whnf ty)).getAppFn | return #[]
    -- Find the inductive constructors of e:
    let some (.inductInfo val) := snap.env.find? name | return #[]
    constructors_rev := val.ctors :: constructors_rev

  let eager : Lsp.CodeAction := {
    title := "Generate a list of equations for this match."
    kind? := "quickfix"
  }

  return #[{ --rest is lightly adapted from eqnStub:
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
          let ctor := l[ctor_idx]!
          let suffix := if constructors_rev.length ≥ 2 then s!"_{ctor_idx + 1}" else ""
          let some pat := pattern_from_constructor ctor snap.env suffix | panic! "bad inductive"
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
  }]

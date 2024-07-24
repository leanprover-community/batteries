/-
Copyright (c) 2023 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Lean.Elab.BuiltinTerm
import Lean.Elab.BuiltinNotation
import Batteries.Lean.Position
import Batteries.CodeAction.Attr
import Lean.Meta.Tactic.TryThis
import Lean.Server.CodeActions.Provider

/-!
# Miscellaneous code actions

This declares some basic tactic code actions, using the `@[tactic_code_action]` API.
-/
namespace Std.CodeAction

open Lean Meta Elab Server RequestM CodeAction

/-- Return the syntax stack leading to `target` from `root`, if one exists. -/
def findStack? (root target : Syntax) : Option Syntax.Stack := do
  let range ← target.getRange?
  root.findStack? (·.getRange?.any (·.includes range))
    (fun s => s.getKind == target.getKind && s.getRange? == range)

/-- Constructs a hole with a kind matching the provided hole elaborator.  -/
def holeKindToHoleString : (elaborator : Name) → (synthName : String) → String
  | ``Elab.Term.elabSyntheticHole, name => "?" ++ name
  | ``Elab.Term.elabSorry, _ => "sorry"
  | _, _ => "_"

/--
Hole code action used to fill in a structure's field when specifying an instance.

In the following:
```lean
instance : Monad Id := _
```

invoking the hole code action "Generate a (minimal) skeleton for the structure under construction."
produces:
```lean
instance : Monad Id where
  pure := _
  bind := _
```

and invoking "Generate a (maximal) skeleton for the structure under construction." produces:
```lean
instance : Monad Id where
  map := _
  mapConst := _
  pure := _
  seq := _
  seqLeft := _
  seqRight := _
  bind := _
```
-/
@[hole_code_action] partial def instanceStub : HoleCodeAction := fun _ snap ctx info => do
  let some ty := info.expectedType? | return #[]
  let .const name _ := (← info.runMetaM ctx (whnf ty)).getAppFn | return #[]
  unless isStructure snap.env name do return #[]
  let doc ← readDoc
  let fields := collectFields snap.env name #[] []
  let only := !fields.any fun (_, auto) => auto
  let mkAutofix minimal :=
    let eager := {
      title := s!"\
        Generate a {if only then "" else if minimal then "(minimal) " else "(maximal) "}\
        skeleton for the structure under construction."
      kind? := "quickfix"
      isPreferred? := minimal
    }
    let lazy? := some do
      let useWhere := do
        let _ :: (stx, _) :: _ ← findStack? snap.stx info.stx | none
        guard (stx.getKind == ``Parser.Command.declValSimple)
        stx[0].getPos?
      let holePos := useWhere.getD info.stx.getPos?.get!
      let (indent, isStart) := findIndentAndIsStart doc.meta.text.source holePos
      let indent := "\n".pushn ' ' indent
      let mut str := if useWhere.isSome then "where" else "{"
      let mut first := useWhere.isNone && isStart
      for (field, auto) in fields do
        if minimal && auto then continue
        if first then
          str := str ++ " "
          first := false
        else
          str := str ++ indent ++ "  "
        let field := toString field
        str := str ++ s!"{field} := {holeKindToHoleString info.elaborator field}"
      if useWhere.isNone then
        if isStart then
          str := str ++ " }"
        else
          str := str ++ indent ++ "}"
      pure { eager with
        edit? := some <| .ofTextEdit doc.versionedIdentifier {
          range := doc.meta.text.utf8RangeToLspRange ⟨holePos, info.stx.getTailPos?.get!⟩
          newText := str
        }
      }
    { eager, lazy? }
  pure <| if only then #[mkAutofix true] else #[mkAutofix true, mkAutofix false]
where
  /-- Returns true if this field is an autoParam or optParam, or if it is given an optional value
  in a child struct. -/
  isAutofillable (env : Environment) (fieldInfo : StructureFieldInfo) (stack : List Name) : Bool :=
    fieldInfo.autoParam?.isSome || env.contains (mkDefaultFnOfProjFn fieldInfo.projFn)
      || stack.any fun struct => env.contains (mkDefaultFnOfProjFn (struct ++ fieldInfo.fieldName))

  /-- Returns the fields of a structure, unfolding parent structures. -/
  collectFields (env : Environment) (structName : Name)
      (fields : Array (Name × Bool)) (stack : List Name) : Array (Name × Bool) :=
    (getStructureFields env structName).foldl (init := fields) fun fields field =>
      if let some fieldInfo := getFieldInfo? env structName field then
        if let some substructName := fieldInfo.subobject? then
          collectFields env substructName fields (structName :: stack)
        else
          fields.push (field, isAutofillable env fieldInfo stack)
      else fields

/-- Returns the explicit arguments given a type. -/
def getExplicitArgs : Expr → Array Name → Array Name
  | .forallE n _ body bi, args =>
    getExplicitArgs body <| if bi.isExplicit then args.push n else args
  | _, args => args

/--
Invoking hole code action "Generate a list of equations for a recursive definition" in the
following:
```lean
def foo : Expr → Unit := _
```

produces:

```lean
def foo : Expr → Unit := fun
  | .bvar deBruijnIndex => _
  | .fvar fvarId => _
  | .mvar mvarId => _
  | .sort u => _
  | .const declName us => _
  | .app fn arg => _
  | .lam binderName binderType body binderInfo => _
  | .forallE binderName binderType body binderInfo => _
  | .letE declName type value body nonDep => _
  | .lit _ => _
  | .mdata data expr => _
  | .proj typeName idx struct => _
```

-/
@[hole_code_action] def eqnStub : HoleCodeAction := fun _ snap ctx info => do
  let some ty := info.expectedType? | return #[]
  let .forallE _ dom .. ← info.runMetaM ctx (whnf ty) | return #[]
  let .const name _ := (← info.runMetaM ctx (whnf dom)).getAppFn | return #[]
  let some (.inductInfo val) := snap.env.find? name | return #[]
  let eager := {
    title := "Generate a list of equations for a recursive definition."
    kind? := "quickfix"
  }
  let doc ← readDoc
  pure #[{
    eager
    lazy? := some do
      let holePos := info.stx.getPos?.get!
      let (indent, isStart) := findIndentAndIsStart doc.meta.text.source holePos
      let mut str := "fun"
      let indent := "\n".pushn ' ' (if isStart then indent else indent + 2)
      for ctor in val.ctors do
        let some (.ctorInfo ci) := snap.env.find? ctor | panic! "bad inductive"
        let ctor := toString (ctor.updatePrefix .anonymous)
        str := str ++ indent ++ s!"| .{ctor}"
        for arg in getExplicitArgs ci.type #[] do
          str := str ++ if arg.hasNum || arg.isInternal then " _" else s!" {arg}"
        str := str ++ s!" => {holeKindToHoleString info.elaborator ctor}"
      pure { eager with
        edit? := some <|.ofTextEdit doc.versionedIdentifier {
          range := doc.meta.text.utf8RangeToLspRange ⟨holePos, info.stx.getTailPos?.get!⟩
          newText := str
        }
      }
  }]

/-- Invoking hole code action "Start a tactic proof" will fill in a hole with `by done`. -/
@[hole_code_action] def startTacticStub : HoleCodeAction := fun _ _ _ info => do
  let holePos := info.stx.getPos?.get!
  let doc ← readDoc
  let indent := (findIndentAndIsStart doc.meta.text.source holePos).1
  pure #[{
    eager.title := "Start a tactic proof."
    eager.kind? := "quickfix"
    eager.edit? := some <|.ofTextEdit doc.versionedIdentifier {
      range := doc.meta.text.utf8RangeToLspRange ⟨holePos, info.stx.getTailPos?.get!⟩
      newText := "by\n".pushn ' ' (indent + 2) ++ "done"
    }
  }]

/-- The "Remove tactics after 'no goals'" code action deletes any tactics following a completed
proof.
```
example : True := by
  trivial
  trivial -- <- remove this, proof is already done
  rfl
```
is transformed to
```
example : True := by
  trivial
```
-/
@[tactic_code_action*]
def removeAfterDoneAction : TacticCodeAction := fun _ _ _ stk node => do
  let .node (.ofTacticInfo info) _ := node | return #[]
  unless info.goalsBefore.isEmpty do return #[]
  let _ :: (seq, i) :: _ := stk | return #[]
  let some stop := seq.getTailPos? | return #[]
  let some prev := (seq.setArgs seq.getArgs[:i]).getTailPos? | return #[]
  let doc ← readDoc
  let eager := {
    title := "Remove tactics after 'no goals'"
    kind? := "quickfix"
    isPreferred? := true
    edit? := some <|.ofTextEdit doc.versionedIdentifier {
      range := doc.meta.text.utf8RangeToLspRange ⟨prev, stop⟩
      newText := ""
    }
  }
  pure #[{ eager }]

/--
Similar to `getElabInfo`, but returns the names of binders instead of just the numbers;
intended for code actions which need to name the binders.
-/
def getElimNames (inductName declName : Name) : MetaM (Array (Name × Array Name)) := do
  let inductVal ← getConstInfoInduct inductName
  let decl ← getConstInfo declName
  forallTelescopeReducing decl.type fun xs type => do
    let motive  := type.getAppFn
    let targets := type.getAppArgs
    let mut altsInfo := #[]
    for i in [inductVal.numParams:xs.size] do
      let x := xs[i]!
      if x != motive && !targets.contains x then
        let xDecl ← x.fvarId!.getDecl
        let args ← forallTelescopeReducing xDecl.type fun args _ => do
          let lctx ← getLCtx
          pure <| args.filterMap fun y =>
            let yDecl := (lctx.find? y.fvarId!).get!
            if yDecl.binderInfo.isExplicit then some yDecl.userName else none
        altsInfo := altsInfo.push (xDecl.userName, args)
    pure altsInfo

/--
Invoking tactic code action "Generate an explicit pattern match for 'induction'" in the
following:
```lean
example (x : Nat) : x = x := by
  induction x
```
produces:
```lean
example (x : Nat) : x = x := by
  induction x with
  | zero => sorry
  | succ n ih => sorry
```

It also works for `cases`.
-/
@[tactic_code_action Parser.Tactic.cases Parser.Tactic.induction]
def casesExpand : TacticCodeAction := fun _ snap ctx _ node => do
  let .node (.ofTacticInfo info) _ := node | return #[]
  let (discr, induction, alts) ← match info.stx with
    | `(tactic| cases $[$_ :]? $e $[$alts:inductionAlts]?) => pure (e, false, alts)
    | `(tactic| induction $e $[generalizing $_*]? $[$alts:inductionAlts]?) => pure (e, true, alts)
    | _ => return #[]
  if let some alts := alts then
    -- this detects the incomplete syntax `cases e with`
    unless alts.raw[2][0][0][0][0].isMissing do return #[]
  let some (.ofTermInfo discrInfo) := node.findInfo? fun i =>
    i.stx.getKind == discr.raw.getKind && i.stx.getRange? == discr.raw.getRange?
    | return #[]
  let .const name _ := (← discrInfo.runMetaM ctx (do whnf (← inferType discrInfo.expr))).getAppFn
    | return #[]
  let tacName := info.stx.getKind.updatePrefix .anonymous
  let eager := {
    title := s!"Generate an explicit pattern match for '{tacName}'."
    kind? := "quickfix"
  }
  let doc ← readDoc
  pure #[{
    eager
    lazy? := some do
      let tacPos := info.stx.getPos?.get!
      let endPos := doc.meta.text.utf8PosToLspPos info.stx.getTailPos?.get!
      let startPos := if alts.isSome then
        let stx' := info.stx.setArg (if induction then 4 else 3) mkNullNode
        doc.meta.text.utf8PosToLspPos stx'.getTailPos?.get!
      else endPos
      let elimName := if induction then mkRecName name else mkCasesOnName name
      let ctors ← discrInfo.runMetaM ctx (getElimNames name elimName)
      let newText := if ctors.isEmpty then "" else Id.run do
        let mut str := " with"
        let indent := "\n".pushn ' ' (findIndentAndIsStart doc.meta.text.source tacPos).1
        for (name, args) in ctors do
          let mut ctor := toString name
          if let some _ := (Parser.getTokenTable snap.env).find? ctor then
            ctor := s!"{idBeginEscape}{ctor}{idEndEscape}"
          str := str ++ indent ++ s!"| {ctor}"
          -- replace n_ih with just ih if there is only one
          let args := if induction &&
            args.foldl (fun c n =>
              if n.eraseMacroScopes.getString!.endsWith "_ih" then c+1 else c) 0 == 1
          then
            args.map (fun n => if !n.hasMacroScopes && n.getString!.endsWith "_ih" then `ih else n)
          else args
          for arg in args do
            str := str ++ if arg.hasNum || arg.isInternal then " _" else s!" {arg}"
          str := str ++ s!" => sorry"
        str
      pure { eager with
        edit? := some <|.ofTextEdit doc.versionedIdentifier {
          range := ⟨startPos, endPos⟩
          newText
        }
      }
  }]

/-- The "Add subgoals" code action puts `· done` subgoals for any goals remaining at the end of a
proof.
```
example : True ∧ True := by
  constructor
  -- <- here
```
is transformed to
```
example : True ∧ True := by
  constructor
  · done
  · done
```
-/
def addSubgoalsActionCore (params : Lsp.CodeActionParams)
  (i : Nat) (stk : Syntax.Stack) (goals : List MVarId) : RequestM (Array LazyCodeAction) := do
  -- If there are zero goals remaining, no need to do anything
  -- If there is one goal remaining, the user can just keep typing and subgoals are not helpful
  unless goals.length > 1 do return #[]
  let seq := stk.head!.1
  let nargs := (seq.getNumArgs + 1) / 2
  unless i == nargs do -- only trigger at the end of a block
    -- or if there is only a `done` or `sorry` terminator
    unless i + 1 == nargs && [
        ``Parser.Tactic.done, ``Parser.Tactic.tacticSorry, ``Parser.Tactic.tacticAdmit
      ].contains seq[2*i].getKind do
      return #[]
  let some startPos := seq[0].getPos? true | return #[]
  let doc ← readDoc
  let eager := { title := "Add subgoals", kind? := "quickfix" }
  pure #[{
    eager
    lazy? := some do
      let indent := "\n".pushn ' ' (doc.meta.text.toPosition startPos).column
      let mut (range, newText) := (default, "")
      if let some tac := seq.getArgs[2*i]? then
        let some range2 := tac.getRange? true | return eager
        range := range2
      else
        let trimmed := seq.modifyArgs (·[:2*i])
        let some tail := trimmed.getTailPos? true | return eager
        (range, newText) := (⟨tail, tail⟩, indent)
        let cursor := doc.meta.text.lspPosToUtf8Pos params.range.end
        if range.stop ≤ cursor && cursor.1 ≤ range.stop.1 + trimmed.getTrailingSize then
          range := { range with stop := cursor }
      newText := newText ++ "· done"
      for _ in goals.tail! do
        newText := newText ++ indent ++ "· done"
      pure { eager with
        edit? := some <|.ofTextEdit doc.versionedIdentifier {
          range := doc.meta.text.utf8RangeToLspRange range
          newText
        }
      }
  }]

@[inherit_doc addSubgoalsActionCore, tactic_code_action]
def addSubgoalsSeqAction : TacticSeqCodeAction := fun params _ _ => addSubgoalsActionCore params

-- This makes sure that the addSubgoals action also triggers
-- when the cursor is on the final `done` of a tactic block
@[inherit_doc addSubgoalsActionCore,
  tactic_code_action Parser.Tactic.done Parser.Tactic.tacticSorry Parser.Tactic.tacticAdmit]
def addSubgoalsAction : TacticCodeAction := fun params _ _ stk node => do
  let (_ :: (seq, i) :: stk@(_ :: t :: _), .node (.ofTacticInfo info) _) := (stk, node) | return #[]
  unless t.1.getKind == ``Parser.Tactic.tacticSeq do return #[]
  addSubgoalsActionCore params (i/2) ((seq, 0) :: stk) info.goalsBefore

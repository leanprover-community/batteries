/-
Copyright (c) 2023 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Std.Lean.Name
import Std.Lean.Position
import Std.CodeAction.Tactic.Basic

/-!
# Miscellaneous tactic code actions

This declares some basic tactic code actions, using the `@[tactic_code_action]` API.
-/
namespace Std.CodeAction

open Lean Meta Elab Server RequestM

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
def removeAfterDoneAction : TacticCodeAction := fun params _ _ stk node => do
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
    edit? := some <|.ofTextEdit params.textDocument.uri {
      range := doc.meta.text.utf8RangeToLspRange ⟨prev, stop⟩
      newText := ""
    }
  }
  pure #[{ eager }]

/--
Similar to `getElabInfo`, but returns the names of binders instead of just the numbers;
intended for code actions which need to name the binders.
-/
def getElimNames (declName : Name) : MetaM (Array (Name × Array Name)) := do
  let decl ← getConstInfo declName
  forallTelescopeReducing decl.type fun xs type => do
    let motive  := type.getAppFn
    let targets := type.getAppArgs
    let mut altsInfo := #[]
    for i in [:xs.size] do
      let x := xs[i]!
      if x != motive && !targets.contains x then
        let xDecl ← x.fvarId!.getDecl
        if xDecl.binderInfo.isExplicit then
          let args ← forallTelescopeReducing xDecl.type fun args _ => do
            let lctx ← getLCtx
            pure <| args.map fun fvar => (lctx.find? fvar.fvarId!).get!.userName
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
def casesExpand : TacticCodeAction := fun params snap ctx _ node => do
  let .node (.ofTacticInfo info) _ := node | return #[]
  let (discr, induction) ← match info.stx with
    | `(tactic| cases $[$_ :]? $e) => pure (e, false)
    | `(tactic| induction $e $[generalizing $_*]?) => pure (e, true)
    | _ => return #[]
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
      let mut str := " with"
      let indent := "\n".pushn ' ' (findIndentAndIsStart doc.meta.text.source tacPos).1
      let elimName := if induction then mkRecName name else mkCasesOnName name
      for (name, args) in ← discrInfo.runMetaM ctx (getElimNames elimName) do
        let mut ctor := toString name
        if let some _ := (Parser.getTokenTable snap.env).find? ctor then
          ctor := s!"{idBeginEscape}{ctor}{idEndEscape}"
        str := str ++ indent ++ s!"| {ctor}"
        -- replace n_ih with just ih if there is only one
        let args := if induction &&
          args.foldl (fun c n => if n.getString!.endsWith "_ih" then c+1 else c) 0 == 1
        then
          args.map (fun n => if n.getString!.endsWith "_ih" then `ih else n)
        else args
        for arg in args do
          str := str ++ if arg.hasNum || arg.isInternal then " _" else s!" {arg}"
        str := str ++ s!" => sorry"
      pure { eager with
        edit? := some <|.ofTextEdit params.textDocument.uri
          { range := ⟨endPos, endPos⟩, newText := str }
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
      let indent := "\n".pushn ' ' (findIndentAndIsStart doc.meta.text.source startPos).1
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
        edit? := some <|.ofTextEdit params.textDocument.uri {
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

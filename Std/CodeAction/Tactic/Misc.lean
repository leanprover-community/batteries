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
      range := doc.meta.text.utf8PosToLspRange prev stop
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
example (e : Nat) : Nat := by
  induction e
```
produces:
```lean
example (e : Nat) : Nat := by
  induction e with
  | zero => done
  | succ n n_ih => done
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
        for arg in args do
          str := str ++ if arg.hasNum || arg.isInternal then " _" else s!" {arg}"
        str := str ++ s!" => done"
      pure { eager with
        edit? := some <|.ofTextEdit params.textDocument.uri
          { range := ⟨endPos, endPos⟩, newText := str }
      }
  }]

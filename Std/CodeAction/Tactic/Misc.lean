/-
Copyright (c) 2023 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Std.Lean.Position
import Std.CodeAction.Tactic.Basic

/-!
# Miscellaneous tactic code actions

This declares some basic tactic code actions, using the `@[tactic_code_action]` API.
-/
namespace Std.CodeAction

open Lean Elab Server RequestM

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

/-
Copyright (c) 2023 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Lean.Elab.BuiltinTerm
import Lean.Elab.BuiltinNotation
import Lean.Server.InfoUtils
import Lean.Server.CodeActions.Provider
import Batteries.CodeAction.Attr

/-!
# Initial setup for code actions

This declares a code action provider that calls all `@[hole_code_action]` definitions
on each occurrence of a hole (`_`, `?_` or `sorry`).

(This is in a separate file from `Batteries.CodeAction.Hole.Attr` so that the server does not
attempt to use this code action provider when browsing the `Batteries.CodeAction.Hole.Attr` file
itself.)
-/
namespace Batteries.CodeAction

open Lean Elab Server RequestM CodeAction

/-- A code action which calls `@[tactic_code_action]` code actions. -/
@[code_action_provider] def tacticCodeActionProvider : CodeActionProvider := fun params snap => do
  let doc ← readDoc
  let startPos := doc.meta.text.lspPosToUtf8Pos params.range.start
  let endPos := doc.meta.text.lspPosToUtf8Pos params.range.end
  let pointerCol :=
    if params.range.start.line == params.range.end.line then
      max params.range.start.character params.range.end.character
    else 0
  let some result := findTactic?
    (fun pos => (doc.meta.text.utf8PosToLspPos pos).character ≤ pointerCol)
    ⟨startPos, endPos⟩ snap.stx | return #[]
  let tgtTac := match result with
    | .tactic (tac :: _)
    | .tacticSeq _ _ (_ :: tac :: _) => tac.1
    | _ => unreachable!
  let tgtRange := tgtTac.getRange?.get!
  have info := findInfoTree? tgtTac.getKind tgtRange none snap.infoTree (canonicalOnly := true)
    fun _ info => info matches .ofTacticInfo _
  let some (ctx, node@(.node (.ofTacticInfo info) _)) := info | return #[]
  let mut out := #[]
  match result with
  | .tactic stk@((tac, _) :: _) => do
    let ctx := { ctx with mctx := info.mctxBefore }
    let actions := (tacticCodeActionExt.getState snap.env).2
    if let some arr := actions.onTactic.find? tac.getKind then
      for act in arr do
        try out := out ++ (← act params snap ctx stk node) catch _ => pure ()
    for act in actions.onAnyTactic do
      try out := out ++ (← act params snap ctx stk node) catch _ => pure ()
  | .tacticSeq _ i stk@((seq, _) :: _) =>
    let (ctx, goals) ← if 2*i < seq.getNumArgs then
      let stx := seq[2*i]
      let some stxRange := stx.getRange? | return #[]
      let some (ctx, .node (.ofTacticInfo info') _) :=
          findInfoTree? stx.getKind stxRange ctx node fun _ info => (info matches .ofTacticInfo _)
        | return #[]
      pure ({ ctx with mctx := info'.mctxBefore }, info'.goalsBefore)
    else
      pure ({ ctx with mctx := info.mctxAfter }, info.goalsAfter)
    for act in (tacticSeqCodeActionExt.getState snap.env).2 do
      try out := out ++ (← act params snap ctx i stk goals) catch _ => pure ()
  | _ => unreachable!
  pure out

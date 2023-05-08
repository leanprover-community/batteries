/-
Copyright (c) 2021 Gabriel Ebner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner, Mario Carneiro
-/
import Lean.Server.CodeActions
import Lean.Widget.UserWidget
import Std.Lean.Name
import Std.Lean.Format
import Std.Lean.Position

/-!
# "Try this" support

This implements a mechanism for tactics to print a message saying `Try this: <suggestion>`,
where `<suggestion>` is a link to a replacement tactic. Users can either click on the link
in the suggestion (provided by a widget), or use a code action which applies the suggestion.
-/
namespace Std.Tactic.TryThis

open Lean Elab Elab.Tactic PrettyPrinter Meta Server Lsp RequestM

/-- An info-tree data node corresponding to an application of the "Try this" command. -/
structure TryThisInfo where
  /-- The suggested replacement for this syntax, usually the rendering of another tactic syntax. -/
  suggestion : String
  /-- This is the span to replace with `suggestion`. If not supplied it will default to
  the span of the syntax on which this info node is placed. -/
  span? : Option (String.Pos × String.Pos) := none
  deriving TypeName

/--
This is a code action provider that looks for `TryThisInfo` nodes and supplies a code action to
apply the replacement.
-/
@[codeActionProvider] def tryThisProvider : CodeActionProvider := fun params snap => do
  let doc ← readDoc
  let startPos := doc.meta.text.lspPosToUtf8Pos params.range.start
  let endPos := doc.meta.text.lspPosToUtf8Pos params.range.end
  pure <| snap.infoTree.foldInfo (init := #[]) fun _ctx info result => Id.run do
    let .ofCustomInfo info := info | result
    let some tti := info.value.get? TryThisInfo | result
    let some (head, tail) := (tti.span? <|> return (← info.stx.getPos?, ← info.stx.getTailPos?))
      | result
    unless head ≤ endPos && startPos ≤ tail do return result
    result.push {
      eager.title := "Apply 'Try this'"
      eager.kind? := "refactor"
      eager.edit? := WorkspaceEdit.ofTextEdit params.textDocument.uri {
        range := doc.meta.text.utf8PosToLspRange head tail
        newText := tti.suggestion
      }
    }

/--
This is a widget which is placed by `TryThis.addSuggestion`; it says `Try this: <replacement>`
where `<replacement>` is a link which will perform the replacement.
-/
@[widget] def tryThisWidget : Widget.UserWidgetDefinition where
  name := "Tactic replacement"
  javascript := "
import * as React from 'react';
import { EditorContext } from '@leanprover/infoview';
const e = React.createElement;
export default function(props) {
  const editorConnection = React.useContext(EditorContext)
  function onClick() {
    editorConnection.api.applyEdit({
      changes: { [props.pos.uri]: [{ range: props.range, newText: props.suggestion }] }
    })
  }
  return e('div', {className: 'ml1'}, e('pre', {className: 'font-code pre-wrap'},
    ['Try this: ', e('a', {onClick, title: 'Apply suggestion'}, props.suggestion)]))
}"

/-- Replace subexpressions like `?m.1234` with `?_` so it can be copy-pasted. -/
partial def replaceMVarsByUnderscores [Monad m] [MonadQuotation m]
    (s : Syntax) : m Syntax :=
  s.replaceM fun s => do
    let `(?$id:ident) := s | pure none
    if id.getId.hasNum || id.getId.isInternal then `(?_) else pure none

/-- Delaborate `e` into an expression suitable for use in `refine`. -/
def delabToRefinableSyntax (e : Expr) : TermElabM Term :=
  return ⟨← replaceMVarsByUnderscores (← delab e)⟩

/-- Add a "try this" suggestion. -/
def addSuggestion (origStx : Syntax) {kind : Name} (suggestion : TSyntax kind)
    (suggestionForMessage : Option MessageData := none)
    (ref? : Option Syntax := none) : MetaM Unit := do
  logInfoAt origStx m!"Try this: {suggestionForMessage.getD suggestion}"
  let map ← getFileMap
  let span? := do let e ← ref?; pure (← e.getPos?, ← e.getTailPos?)
  let span?' := span? <|> return (← origStx.getPos?, ← origStx.getTailPos?)
  let text ← PrettyPrinter.ppCategory kind suggestion
  let (indent, column) := if let some (pos, _) := span?' then
    let start := findLineStart map.source pos
    let body := map.source.findAux (· ≠ ' ') pos start
    ((body - start).1, (pos - start).1)
  else (0, 0)
  let text := Format.prettyExtra text (indent := indent) (column := column)
  pushInfoLeaf <| .ofCustomInfo {
    stx := origStx
    value := Dynamic.mk (TryThisInfo.mk text span?)
  }
  if let some (head, tail) := span?' then
    let range := Lsp.Range.mk (map.utf8PosToLspPos head) (map.utf8PosToLspPos tail)
    let json := Json.mkObj [("suggestion", text), ("range", toJson range)]
    Widget.saveWidgetInfo ``tryThisWidget json origStx

/-- Add a `exact e` or `refine e` suggestion. -/
def addExactSuggestion (origTac : Syntax) (e : Expr)
    (ref? : Option Syntax := none) : TermElabM Unit := do
  let stx ← delabToRefinableSyntax e
  let tac ← if e.hasExprMVar then `(tactic| refine $stx) else `(tactic| exact $stx)
  let msg := if e.hasExprMVar then m!"refine {e}" else m!"exact {e}"
  addSuggestion origTac tac (suggestionForMessage := msg) (ref? := ref?)

/-- Add a term suggestion. -/
def addTermSuggestion (origTerm : Syntax) (e : Expr)
    (ref? : Option Syntax := none) : TermElabM Unit := do
  addSuggestion origTerm (← delabToRefinableSyntax e) (suggestionForMessage := e) (ref? := ref?)

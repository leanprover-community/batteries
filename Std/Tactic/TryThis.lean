/-
Copyright (c) 2021 Gabriel Ebner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner, Mario Carneiro
-/
import Lean.Server.CodeActions
import Lean.Widget.UserWidget
import Std.Lean.Name
import Std.Lean.Position

/-!
# "Try this" support

This implements a mechanism for tactics to print a message saying `Try this: <suggestion>`,
where `<suggestion>` is a link to a replacement tactic. Users can either click on the link
in the suggestion (provided by a widget), or use a code action which applies the suggestion.
-/
namespace Std.Tactic.TryThis

open Lean Elab PrettyPrinter Meta Server RequestM

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
  return e('div', {className: 'ml1'}, e('pre', {className: 'font-code pre-wrap'}, [
    'Try this: ',
    e('a', {onClick, className: 'link pointer dim', title: 'Apply suggestion'}, props.suggestion),
    props.info
  ]))
}"

/--
This is a code action provider that looks for `TryThisInfo` nodes and supplies a code action to
apply the replacement.
-/
@[codeActionProvider] def tryThisProvider : CodeActionProvider := fun params snap => do
  let doc ← readDoc
  pure <| snap.infoTree.foldInfo (init := #[]) fun _ctx info result => Id.run do
    let .ofUserWidgetInfo { stx, widgetId := ``tryThisWidget, props } := info | result
    let some stxRange := stx.getRange? | result
    let stxRange := doc.meta.text.utf8RangeToLspRange stxRange
    unless stxRange.start.line ≤ params.range.end.line do return result
    unless params.range.start.line ≤ stxRange.end.line do return result
    let .ok newText := props.getObjValAs? String "suggestion" | panic! "bad type"
    let .ok range := props.getObjValAs? Lsp.Range "range" | panic! "bad type"
    result.push {
      eager.title := "Apply 'Try this'"
      eager.kind? := "refactor"
      eager.edit? := some <| .ofTextEdit params.textDocument.uri { range, newText }
    }

/-- Replace subexpressions like `?m.1234` with `?_` so it can be copy-pasted. -/
partial def replaceMVarsByUnderscores [Monad m] [MonadQuotation m]
    (s : Syntax) : m Syntax :=
  s.replaceM fun s => do
    let `(?$id:ident) := s | pure none
    if id.getId.hasNum || id.getId.isInternal then `(?_) else pure none

/-- Delaborate `e` into an expression suitable for use in `refine`. -/
def delabToRefinableSyntax (e : Expr) : TermElabM Term :=
  return ⟨← replaceMVarsByUnderscores (← delab e)⟩

/-- Add a "try this" suggestion. This has three effects:

* An info diagnostic is displayed saying `Try this: <suggestion>`
* A widget is registered, saying `Try this: <suggestion>` with a link on `<suggestion>` to apply
  the suggestion
* A code action `Apply 'Try this'` is added, which will apply the suggestion.

The parameters are:
* `ref`: the span of the info diagnostic
* `suggestion`: the replacement syntax
* `suggestionForMessage?`: the message to display in the info diagnostic (only).
  The widget message uses only `suggestion`. If not provided, `suggestion` is used in both places.
* `origSpan?`: a syntax object whose span is the actual text to be replaced by `suggestion`.
  If not provided it defaults to `ref`.
* `extraMsg`: an extra piece of message text to apply to the widget message (only).
-/
def addSuggestion (ref : Syntax) {kind : Name} (suggestion : TSyntax kind)
    (suggestionForMessage? : Option MessageData := none)
    (origSpan? : Option Syntax := none)
    (extraMsg : String := "") : MetaM Unit := do
  logInfoAt ref m!"Try this: {suggestionForMessage?.getD suggestion}"
  -- TODO: use the right indentation
  let text := Format.pretty (← PrettyPrinter.ppCategory kind suggestion)
  if let some range := (origSpan?.getD ref).getRange? then
    let stxRange := ref.getRange?.getD range
    let map ← getFileMap
    let stxRange :=
    { start := map.lineStart (map.toPosition stxRange.start).line
      stop := map.lineStart ((map.toPosition stxRange.stop).line + 1) }
    let range := map.utf8RangeToLspRange range
    let json := Json.mkObj [("suggestion", text), ("range", toJson range), ("info", extraMsg)]
    Widget.saveWidgetInfo ``tryThisWidget json (.ofRange stxRange)

/-- Add a `exact e` or `refine e` suggestion.

The parameters are:
* `ref`: the span of the info diagnostic
* `e`: the replacement expression
* `origSpan?`: a syntax object whose span is the actual text to be replaced by `suggestion`.
  If not provided it defaults to `ref`.
-/
def addExactSuggestion (ref : Syntax) (e : Expr)
    (origSpan? : Option Syntax := none) : TermElabM Unit := do
  let stx ← delabToRefinableSyntax e
  let mvars ← getMVars e
  let tac ← if mvars.isEmpty then `(tactic| exact $stx) else `(tactic| refine $stx)
  let (msg, extraMsg) ← if mvars.isEmpty then pure (m!"exact {e}", "") else
    let mut str := "\nRemaining subgoals:"
    for g in mvars do
      -- TODO: use a MessageData.ofExpr instead of rendering to string
      let e ← PrettyPrinter.ppExpr (← instantiateMVars (← g.getType))
      str := str ++ Format.pretty ("\n⊢ " ++ e)
    pure (m!"refine {e}", str)
  addSuggestion ref tac (suggestionForMessage? := msg)
    (origSpan? := origSpan?) (extraMsg := extraMsg)

/-- Add a term suggestion.

The parameters are:
* `ref`: the span of the info diagnostic
* `e`: the replacement expression
* `origSpan?`: a syntax object whose span is the actual text to be replaced by `suggestion`.
  If not provided it defaults to `ref`.
-/
def addTermSuggestion (ref : Syntax) (e : Expr)
    (origSpan? : Option Syntax := none) : TermElabM Unit := do
  addSuggestion ref (← delabToRefinableSyntax e)
    (suggestionForMessage? := e) (origSpan? := origSpan?)

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
    props.header,
    e('a', {onClick, className: 'link pointer dim', title: 'Apply suggestion'}, props.suggestion),
    props.info
  ]))
}"

/--
This is a widget which is placed by `TryThis.addSuggestions`; it says
```
Try these:
```
* `<replacement1>`
* `<replacement2>`
* `<replacement3>`
* ...

where `<replacement*>` is a link which will perform the replacement.
-/
@[widget] def tryTheseWidget : Widget.UserWidgetDefinition where
  name := "Tactic replacements"
  javascript := "
import * as React from 'react';
import { EditorContext } from '@leanprover/infoview';
const e = React.createElement;
export default function(props) {
  const editorConnection = React.useContext(EditorContext)

  function makeSuggestion({suggestion, info}) {
    function onClick() {
      editorConnection.api.applyEdit({
        changes: { [props.pos.uri]: [{ range: props.range, newText: suggestion }] }
      })
    }
    return e('li', {className:'font-code pre-wrap'},
        e('a',
          {onClick, className: 'link pointer dim', title: 'Apply suggestion'},
          suggestion),
        info
    )
  }
  const s = props.suggestions.map(makeSuggestion)
  return e('div', {className: 'ml1'},
    e('pre', {className: 'font-code pre-wrap'}, props.header),
    e('ul', {style:{paddingInlineStart:'20px'}}, s)
  )
}"

/--
This is a code action provider that looks for `TryThisInfo` nodes and supplies a code action to
apply the replacement.
-/
@[code_action_provider] def tryThisProvider : CodeActionProvider := fun params snap => do
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
      eager.title := "Try this: " ++ newText
      eager.kind? := "refactor"
      eager.edit? := some <| .ofTextEdit params.textDocument.uri { range, newText }
    }

/--
This is a code action provider that looks for `TryTheseInfo` nodes and supplies code actions for
each replacement.
-/
@[code_action_provider] def tryTheseProvider : CodeActionProvider := fun params snap => do
  let doc ← readDoc
  pure <| snap.infoTree.foldInfo (init := #[]) fun _ctx info result => Id.run do
    let .ofUserWidgetInfo { stx, widgetId := ``tryTheseWidget, props } := info | result
    let some stxRange := stx.getRange? | result
    let stxRange := doc.meta.text.utf8RangeToLspRange stxRange
    unless stxRange.start.line ≤ params.range.end.line do return result
    unless params.range.start.line ≤ stxRange.end.line do return result
    let .ok range := props.getObjValAs? Lsp.Range "range" | panic! "bad type"
    let .ok suggestions := props.getObjVal? "suggestions" | panic! "bad type"
    let .ok suggestions := suggestions.getArr? | panic! "bad type"
    suggestions.foldlM (init := result) fun result s => do
      let .ok newText := s.getObjValAs? String "suggestion" | panic! "bad type"
      result.push {
        eager.title := "Try this: " ++ newText
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
* A code action is added, which will apply the suggestion.

The parameters are:
* `ref`: the span of the info diagnostic
* `suggestion`: the replacement syntax
* `suggestionForMessage?`: the message to display in the info diagnostic (only).
  The widget message uses only `suggestion`. If not provided, `suggestion` is used in both places.
* `origSpan?`: a syntax object whose span is the actual text to be replaced by `suggestion`.
  If not provided it defaults to `ref`.
* `extraMsg`: an extra piece of message text to apply to the widget message (only).
* `header`: a string that begins the display. By default, it is `"Try this: "`.
-/
def addSuggestion (ref : Syntax) {kind : Name} (suggestion : TSyntax kind)
    (suggestionForMessage? : Option MessageData := none)
    (origSpan? : Option Syntax := none)
    (extraMsg : String := "")
    (header : String := "Try this: ") : MetaM Unit := do
  logInfoAt ref m!"{header}{suggestionForMessage?.getD suggestion}"
  if let some range := (origSpan?.getD ref).getRange? then
    let map ← getFileMap
    let text ← PrettyPrinter.ppCategory kind suggestion
    let start := findLineStart map.source range.start
    let body := map.source.findAux (· ≠ ' ') range.start start
    let text := Format.prettyExtra text
      (indent := (body - start).1) (column := (range.start - start).1)
    let stxRange := ref.getRange?.getD range
    let stxRange :=
    { start := map.lineStart (map.toPosition stxRange.start).line
      stop := map.lineStart ((map.toPosition stxRange.stop).line + 1) }
    let range := map.utf8RangeToLspRange range
    let json := Json.mkObj [("suggestion", text), ("range", toJson range), ("info", extraMsg),
      ("header", header)]
    Widget.saveWidgetInfo ``tryThisWidget json (.ofRange stxRange)

/-- Holds a `suggestion` for replacement, along with an `info` string to be printed immediately
after that suggestion and optional `MessageData` to represent the suggestion in logs. -/
structure Suggestion (kind : Name) where
  /-- Syntax to be used as a replacement via a code action. -/
  suggestion : TSyntax kind
  /-- Info to be printed immediately after replacement syntax. -/
  info : String := ""
  /-- How to represent the suggestion as `MessageData`. This is used only in the info diagnostic.
  If `none`, we use `suggestion`. -/
  messageData : Option MessageData := none

instance {kind : Name} : Coe (TSyntax kind) (Suggestion kind) where
  coe t := { suggestion := t }

/-- Add a list of "try this" suggestions as a single "try these" suggestion. This has three effects:

* An info diagnostic is displayed saying `Try these: <list of suggestions>`
* A widget is registered, saying `Try these: <list of suggestions>` with a link on each
  `<suggestion>` to apply the suggestion
* A code action for each suggestion is added, which will apply the suggestion.

The parameters are:
* `ref`: the span of the info diagnostic
* `suggestions`: an array of `Suggestion`s, which each contain
  * `suggestion`: the replacement syntax
  * `info`: a string shown immediately after the replacement syntax in the infoview
* `suggestionsForMessage?`: the messages to display in the info diagnostic (only).
  The widget message uses only `suggestion`. If empty or too short, `suggestion` is used in both
  places.
* `origSpan?`: a syntax object whose span is the actual text to be replaced by `suggestion`.
  If not provided it defaults to `ref`.
* `header`: a string that precedes the list. By default, it is `"Try these:"`.
-/
def addSuggestions (ref : Syntax) {kind : Name} (suggestions : Array (Suggestion kind))
    (origSpan? : Option Syntax := none)
    (header : String := "Try these:") : MetaM Unit := do
  let msgs := suggestions.map fun s => s.messageData.getD s.suggestion
  let msgs := msgs.foldl (init := MessageData.nil) (fun msg m => msg ++ m!"\n• " ++ m)
  logInfoAt ref m!"{header}{msgs}"
  if let some range := (origSpan?.getD ref).getRange? then
    let map ← getFileMap
    let start := findLineStart map.source range.start
    let body := map.source.findAux (· ≠ ' ') range.start start
    let suggestions ← suggestions.mapM fun ⟨suggestion, info, _⟩ => do
      let text ← PrettyPrinter.ppCategory kind suggestion
      let text := Format.prettyExtra text
        (indent := (body - start).1) (column := (range.start - start).1)
      pure <| Json.mkObj [("suggestion", text), ("info", info)]
    let stxRange := ref.getRange?.getD range
    let stxRange :=
    { start := map.lineStart (map.toPosition stxRange.start).line
      stop := map.lineStart ((map.toPosition stxRange.stop).line + 1) }
    let range := map.utf8RangeToLspRange range
    let json := Json.mkObj [("suggestions", Json.arr suggestions), ("range", toJson range),
      ("header", header)]
    Widget.saveWidgetInfo ``tryTheseWidget json (.ofRange stxRange)

private def addExactSuggestionCore (addSubgoalsMsg : Bool) (e : Expr) :
    TermElabM (Suggestion `tactic) := do
  let stx ← delabToRefinableSyntax e
  let mvars ← getMVars e
  let tac ← if mvars.isEmpty then `(tactic| exact $stx) else `(tactic| refine $stx)
  let msg := if mvars.isEmpty then m!"exact {e}" else m!"refine {e}"
  let info ← if !addSubgoalsMsg || mvars.isEmpty then pure "" else
    let mut str := "\nRemaining subgoals:"
    for g in mvars do
      -- TODO: use a MessageData.ofExpr instead of rendering to string
      let e ← PrettyPrinter.ppExpr (← instantiateMVars (← g.getType))
      str := str ++ Format.pretty ("\n⊢ " ++ e)
    pure str
  pure ⟨tac, info, msg⟩

/-- Add an `exact e` or `refine e` suggestion.

The parameters are:
* `ref`: the span of the info diagnostic
* `e`: the replacement expression
* `origSpan?`: a syntax object whose span is the actual text to be replaced by `suggestion`.
  If not provided it defaults to `ref`.
-/
def addExactSuggestion (ref : Syntax) (e : Expr)
    (origSpan? : Option Syntax := none) (addSubgoalsMsg := false) : TermElabM Unit := do
  let ⟨tac, extraMsg, msg⟩ ← addExactSuggestionCore addSubgoalsMsg e
  addSuggestion ref tac (suggestionForMessage? := msg)
    (origSpan? := origSpan?) (extraMsg := extraMsg)

/-- Add `exact e` or `refine e` suggestions.

The parameters are:
* `ref`: the span of the info diagnostic
* `es`: the array of replacement expressions
* `origSpan?`: a syntax object whose span is the actual text to be replaced by `suggestion`.
  If not provided it defaults to `ref`.
-/
def addExactSuggestions (ref : Syntax) (es : Array Expr)
    (origSpan? : Option Syntax := none) (addSubgoalsMsg := false) : TermElabM Unit := do
  let suggestions ← es.mapM <| addExactSuggestionCore addSubgoalsMsg
  addSuggestions ref suggestions (origSpan? := origSpan?)

/-- Add a term suggestion.

The parameters are:
* `ref`: the span of the info diagnostic
* `e`: the replacement expression
* `origSpan?`: a syntax object whose span is the actual text to be replaced by `suggestion`.
  If not provided it defaults to `ref`.
* `header`: a string which precedes the suggestion. By default, it's `"Try this: "`.
-/
def addTermSuggestion (ref : Syntax) (e : Expr)
    (origSpan? : Option Syntax := none) (header : String := "Try this: ") : TermElabM Unit := do
  addSuggestion ref (← delabToRefinableSyntax e)
    (suggestionForMessage? := e) (origSpan? := origSpan?) (header := header)

/-- Add term suggestions.

The parameters are:
* `ref`: the span of the info diagnostic
* `es`: an array of the replacement expressions
* `origSpan?`: a syntax object whose span is the actual text to be replaced by `suggestion`.
  If not provided it defaults to `ref`.
* `header`: a string which precedes the list of suggestions. By default, it's `"Try these:"`.
-/
def addTermSuggestions (ref : Syntax) (es : Array Expr)
    (origSpan? : Option Syntax := none) (header : String := "Try these:") : TermElabM Unit := do
  addSuggestions ref (← es.mapM (β := Suggestion `term) (delabToRefinableSyntax ·))
    (origSpan? := origSpan?) (header := header)

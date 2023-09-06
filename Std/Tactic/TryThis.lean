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

/-! # Raw widgets and code actions -/

/-- A JS function which constructs the explicit style of the suggestion given the object
corresponding to its `SuggestionStyle`. -/
def getStyleFunction := "
  function getStyle(style) {
    return style === null ? {
        className:'link pointer dim',
        style:{color:'var(--vscode-textLink-foreground)'}
      }
      : style?.error ? (
        style.error.decorated ? {
          className:'pointer dim',
          style:{
            color:'var(--vscode-errorForeground)',
            textDecoration:'underline wavy var(--vscode-editorError-foreground) 1pt'
          }
        }
        : {className:'pointer dim', style:{color:'var(--vscode-errorForeground)'}}
      )
      : style?.warning ? (
        style.warning.decorated ? {
          className:'gold pointer dim',
          style:{textDecoration:'underline wavy var(--vscode-editorWarning-foreground) 1pt'}
        }
        : {className:'gold pointer dim'}
      )
      : style === 'success' ? {className:'information pointer dim'}
      : style === 'asHypothesis' ? {className:'goal-hyp pointer dim'}
      : style === 'asInaccessible' ? {className:'goal-inaccessible pointer dim'}
      : style?.value ? {
        className:'pointer dim',
        style:{color:`hsl(${Math.round(Math.min(Math.max(style.value.t,0),1) * 120)} 95% 60%)`},
        title:(style.value.showValueInHoverText
          ? `Apply suggestion (${Math.min(Math.max(style.value.t,0),1)})`
          : 'Apply suggestion')
      }
      : {
        className:'link pointer dim',
        style:{border:'solid thin red'},
        title:'An unexpected styling error has occurred.'
          + 'Please report this on the std4 repo or on Zulip.'
        }
  }
"

/--
This is a widget which is placed by `TryThis.addSuggestion`; it says `Try this: <replacement>`
where `<replacement>` is a link which will perform the replacement.
-/
@[widget] def tryThisWidget : Widget.UserWidgetDefinition where
  name := "Suggestion"
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
  }" ++ getStyleFunction ++ "

  return e('div', {className: 'ml1'},
    e('pre', {className: 'font-code pre-wrap'}, [
      props.header,
      props.preInfo,
      e('span',
        {onClick, title: 'Apply suggestion', ...getStyle(props.style)},
        props.suggestion),
      props.postInfo
    ])
  )
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
  name := "Suggestions"
  javascript := "
import * as React from 'react';
import { EditorContext } from '@leanprover/infoview';
const e = React.createElement;
export default function(props) {
  const editorConnection = React.useContext(EditorContext)" ++ getStyleFunction ++ "

  function makeSuggestion({suggestion, preInfo, postInfo, style}) {
    function onClick() {
      editorConnection.api.applyEdit({
        changes: { [props.pos.uri]: [{ range: props.range, newText: suggestion }] }
      })
    }
    return e('li', {className:'font-code pre-wrap'},
      preInfo,
      e('span',
        {onClick, title: 'Apply suggestion', ...getStyle(style)},
        suggestion),
      postInfo
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

/-! # `Suggestion` data -/

-- TODO: we could also support `Syntax` and `Format`
/-- Text to be used as a suggested replacement in the infoview. This can be either a `TSyntax kind`
for a single `kind : SyntaxNodeKind` or a raw `String`.

Instead of using constructors directly, there are coercions available from these types to
`SuggestionText`. -/
inductive SuggestionText where
/-- `TSyntax kind` used as suggested replacement text in the infoview. Note that while `TSyntax` is
in general parameterized by a list of `SyntaxNodeKind`s, we only allow one here; this unambiguously
guides pretty-printing. -/
| tsyntax {kind : SyntaxNodeKind} : TSyntax kind → SuggestionText
/-- A raw string to be used as suggested replacement text in the infoview. -/
| string : String → SuggestionText
deriving Repr, Inhabited

instance : BEq SuggestionText where
  beq
  | .tsyntax (kind := kind₁) stx₁, .tsyntax (kind := kind₂) stx₂ =>
    kind₁ == kind₂ && stx₁.raw == stx₂.raw
  | .string s₁, .string s₂ => s₁ == s₂
  | _, _ => false

instance : ToMessageData SuggestionText where
  toMessageData
  | .tsyntax stx => stx
  | .string s => s

instance {kind : SyntaxNodeKind} : CoeHead (TSyntax kind) SuggestionText where
  coe t := .tsyntax t

instance : Coe String SuggestionText where
  coe := .string

namespace SuggestionText

/-- `true` when `SuggestionText` is underlyingly a `TSyntax`. -/
def isTSyntax : SuggestionText → Bool
| .tsyntax _ => true
| _ => false

/-- `true` when `SuggestionText` is underlyingly a `String`. -/
def isString : SuggestionText → Bool
| .string _ => true
| _ => false

/-- Gets the underlying `TSyntax` of a `SuggestionText` if there is one. -/
def getTSyntax? : SuggestionText → Option ((kind : SyntaxNodeKind) × TSyntax kind)
| .tsyntax (kind := kind) stx => some ⟨kind, stx⟩
| _ => none

/-- Gets the underlying `String` of a `SuggestionText` if there is one. -/
def getString? : SuggestionText → Option String
| .string s => s
| _ => none

/-- Pretty-prints a `SuggestionText` as a `Format`. If the `SuggestionText` is some `TSyntax kind`,
we use the appropriate pretty-printer; strings are coerced to `Format`s as-is. -/
def pretty : SuggestionText → CoreM Format
| .tsyntax (kind := kind) stx =>
  PrettyPrinter.ppCategory kind stx
| .string text => return text

/- Note that this is essentially `return (← s.pretty).prettyExtra w indent column`, but we special-case strings to avoid converting them to `Format`s and back. -/
/-- Pretty-prints a `SuggestionText` as a `String` and wraps with respect to the pane width,
indentation, and column, via `Format.prettyExtra`. Raw `String`s are returned as-is. -/
def prettyExtra (s : SuggestionText) (w : Nat := Format.defWidth)
    (indent column : Nat := 0) : CoreM String :=
  match s with
  | .tsyntax (kind := kind) stx =>
    return (← PrettyPrinter.ppCategory kind stx).prettyExtra w indent column
  | .string text => return text

end SuggestionText

/-- Style hooks for `Suggestion`s. The possible values are
* `.error`; takes an optional boolean argument which determines whether to show an error squiggle
(true by default)
* `.warning`; takes an optional boolean argument which determines whether to show a warning
squiggle (true by default)
* `.success`
* `.asHypothesis`, the style of goal hypotheses
* `.asInaccessible`, the style of inaccessible goal hypotheses
* `.value t` where `t : Float`, which draws from a red-yellow-green gradient with red at `t = 0.0`
and green at `t = 1.0`. `t` is assumed to be between `0.0` and `1.0`. Values outside this range are
silently clipped to lie within this range. An optional boolean argument may be supplied which
determines whether to include the value `t` in hover text (`true` by default).
-/
inductive SuggestionStyle where
/-- Style as an error. By default, decorates the text with an undersquiggle; providing the argument
`decorated := false` turns this off. -/
-- The VS code error foreground theme color (`--vscode-errorForeground`).
| error (decorated := true)
/-- Style as a warning. By default, decorates the text with an undersquiggle; providing the
argument `decorated := false` turns this off. -/
-- The `.gold` CSS class, which the infoview uses when e.g. building a file.
| warning (decorated := true)
/-- Style as a success. -/
-- The `.information` CSS class, which the infoview uses on successes.
| success
/-- Style the same way as a hypothesis appearing in the infoview. -/
-- The `.goal-hyp` CSS class.
| asHypothesis
/-- Style the same way as an inaccessible hypothesis appearing in the infoview. -/
-- The `.goal-inaccessible` CSS class.
| asInaccessible
/-- Draws the color from a red-yellow-green color gradient with red at `0.0`, yellow at `0.5`, and
green at `1.0`. Values outside the range `[0.0, 1.0]` are clipped to lie within this range.

With `showValueInHoverText := true` (the default), the value `t` will be included in the `title` of
the HTML element (which appears on hover). -/
/- interpolates linearly from 0º to 120º along the 95% saturation, 60% lightness contour in HSL
space. -/
| value (t : Float) (showValueInHoverText := true)
deriving Inhabited, Repr, ToJson, FromJson

/-- Holds a `suggestion` for replacement, along with `preInfo` and `postInfo` strings to be printed
immediately before and after that suggestion, respectively. It also includes an optional
`MessageData` to represent the suggestion in logs; by default, this is `none`, and `suggestion` is
used. -/
structure Suggestion where
  /-- Text to be used as a replacement via a code action. -/
  suggestion : SuggestionText
  /-- Info to be printed immediately before replacement text in a widget. -/
  preInfo : String := ""
  /-- Info to be printed immediately after replacement text in a widget. -/
  postInfo : String := ""
  /-- Optional style specification for the suggestion. If `none` (the default), the suggestion is
  styled as a text link. Otherwise, the suggestion can be styled as:
  * a status: `.error`, `.warning`, `.success`
  * a hypothesis name: `.asHypothesis`, `.asInaccessible`
  * a variable color: `.value (t : Float)`, which draws from a red-yellow-green gradient, with red
  at `0.0` and green at `1.0`.

  See `SuggestionStyle` for details. -/
  style? : Option SuggestionStyle := none
  /-- How to represent the suggestion as `MessageData`. This is used only in the info diagnostic.
  If `none`, we use `suggestion`. Use `toMessageData` to render a `Suggestion` in this manner. -/
  messageData? : Option MessageData := none
deriving Inhabited

/- If `messageData?` is specified, we use that; otherwise (by default), we use `toMessageData` of
the suggestion text. -/
instance : ToMessageData Suggestion where
  toMessageData s := s.messageData?.getD (toMessageData s.suggestion)

instance : Coe SuggestionText Suggestion where
  coe t := { suggestion := t }

/-! # Formatting -/

/-- Yields `(indent, column)` given a `FileMap` and a `String.Range`, where `indent` is the number
of spaces by which the line that first includes `range` is initially indented, and `column` is the
column `range` starts at in that line. -/
def getIndentAndColumn (map : FileMap) (range : String.Range) : Nat × Nat :=
  let start := findLineStart map.source range.start
  let body := map.source.findAux (· ≠ ' ') range.start start
  ((body - start).1, (range.start - start).1)

/-- Replace subexpressions like `?m.1234` with `?_` so it can be copy-pasted. -/
partial def replaceMVarsByUnderscores [Monad m] [MonadQuotation m]
    (s : Syntax) : m Syntax :=
  s.replaceM fun s => do
    let `(?$id:ident) := s | pure none
    if id.getId.hasNum || id.getId.isInternal then `(?_) else pure none

/-- Delaborate `e` into an expression suitable for use in `refine`. -/
def delabToRefinableSyntax (e : Expr) : TermElabM Term :=
  return ⟨← replaceMVarsByUnderscores (← delab e)⟩

/-- Delaborate `e` into a suggestion suitable for use in `refine`. -/
def delabToRefinableSuggestion (e : Expr) : TermElabM Suggestion :=
  return { suggestion := ← delabToRefinableSyntax e, messageData? := e }

/-! # Widget hooks -/

/-- Add a "try this" suggestion. This has three effects:

* An info diagnostic is displayed saying `Try this: <suggestion>`
* A widget is registered, saying `Try this: <suggestion>` with a link on `<suggestion>` to apply
  the suggestion
* A code action is added, which will apply the suggestion.

The parameters are:
* `ref`: the span of the info diagnostic
* `s`: a `Suggestion`, which contains
  * `suggestion`: the replacement text;
  * `preInfo`: a string shown immediately after the replacement text in the widget message (only)
  * `postInfo`: a string shown immediately after the replacement text in the widget message (only)
  * `style?`: an optional `Json` object used as the value of the `style` attribute of the
    suggestion text's element (not the whole suggestion element).
  * `messageData?`: an optional message to display in place of `suggestion` in the info diagnostic
    (only). The widget message uses only `suggestion`. If `messageData?` is `none`, we simply use
    `suggestion` instead.
* `origSpan?`: a syntax object whose span is the actual text to be replaced by `suggestion`.
  If not provided it defaults to `ref`.
* `header`: a string that begins the display. By default, it is `"Try this: "`.
-/
def addSuggestion (ref : Syntax) (s : Suggestion)
    (origSpan? : Option Syntax := none)
    (header : String := "Try this: ") : CoreM Unit := do
  logInfoAt ref m!"{header}{s}"
  if let some range := (origSpan?.getD ref).getRange? then
    let map ← getFileMap
    let (indent, column) := getIndentAndColumn map range
    let text ← s.suggestion.prettyExtra (indent := indent) (column := column)
    let stxRange := ref.getRange?.getD range
    let stxRange :=
    { start := map.lineStart (map.toPosition stxRange.start).line
      stop := map.lineStart ((map.toPosition stxRange.stop).line + 1) }
    let range := map.utf8RangeToLspRange range
    let json := Json.mkObj [("suggestion", text), ("range", toJson range),
      ("preInfo", s.preInfo), ("postInfo", s.postInfo), ("style", toJson s.style?),
      ("header", header)]
    Widget.saveWidgetInfo ``tryThisWidget json (.ofRange stxRange)

/-- Add a list of "try this" suggestions as a single "try these" suggestion. This has three effects:

* An info diagnostic is displayed saying `Try these: <list of suggestions>`
* A widget is registered, saying `Try these: <list of suggestions>` with a link on each
  `<suggestion>` to apply the suggestion
* A code action for each suggestion is added, which will apply the suggestion.

The parameters are:
* `ref`: the span of the info diagnostic
* `suggestions`: an array of `Suggestion`s, which each contain
  * `suggestion`: the replacement text;
  * `preInfo`: a string shown immediately after the replacement text in the widget message (only)
  * `postInfo`: a string shown immediately after the replacement text in the widget message (only)
  * `style?`: an optional `Json` object used as the value of the `style` attribute of the
    suggestion text's element (not the whole suggestion element).
  * `messageData?`: an optional message to display in place of `suggestion` in the info diagnostic
    (only). The widget message uses only `suggestion`. If `messageData?` is `none`, we simply use
    `suggestion` instead.
* `origSpan?`: a syntax object whose span is the actual text to be replaced by `suggestion`.
  If not provided it defaults to `ref`.
* `header`: a string that precedes the list. By default, it is `"Try these:"`.
-/
def addSuggestions (ref : Syntax) (suggestions : Array Suggestion)
    (origSpan? : Option Syntax := none)
    (header : String := "Try these:") : CoreM Unit := do
  let msgs := suggestions.map toMessageData
  let msgs := msgs.foldl (init := MessageData.nil) (fun msg m => msg ++ m!"\n• " ++ m)
  logInfoAt ref m!"{header}{msgs}"
  if let some range := (origSpan?.getD ref).getRange? then
    let map ← getFileMap
    let (indent, column) := getIndentAndColumn map range
    let suggestions ←
      suggestions.mapM fun { suggestion, preInfo, postInfo, style?, .. } => do
        let text ← suggestion.prettyExtra (indent := indent) (column := column)
        pure <| Json.mkObj [("suggestion", text), ("preInfo", preInfo), ("postInfo", postInfo),
          ("style", toJson style?)]
    let stxRange := ref.getRange?.getD range
    let stxRange :=
    { start := map.lineStart (map.toPosition stxRange.start).line
      stop := map.lineStart ((map.toPosition stxRange.stop).line + 1) }
    let range := map.utf8RangeToLspRange range
    let json := Json.mkObj [("suggestions", Json.arr suggestions), ("range", toJson range),
      ("header", header)]
    Widget.saveWidgetInfo ``tryTheseWidget json (.ofRange stxRange)

private def addExactSuggestionCore (addSubgoalsMsg : Bool) (e : Expr) : TermElabM Suggestion := do
  let stx ← delabToRefinableSyntax e
  let mvars ← getMVars e
  let suggestion ← if mvars.isEmpty then `(tactic| exact $stx) else `(tactic| refine $stx)
  let messageData? := if mvars.isEmpty then m!"exact {e}" else m!"refine {e}"
  let postInfo ← if !addSubgoalsMsg || mvars.isEmpty then pure "" else
    let mut str := "\nRemaining subgoals:"
    for g in mvars do
      -- TODO: use a MessageData.ofExpr instead of rendering to string
      let e ← PrettyPrinter.ppExpr (← instantiateMVars (← g.getType))
      str := str ++ Format.pretty ("\n⊢ " ++ e)
    pure str
  pure { suggestion, postInfo, messageData? }

/-- Add an `exact e` or `refine e` suggestion.

The parameters are:
* `ref`: the span of the info diagnostic
* `e`: the replacement expression
* `origSpan?`: a syntax object whose span is the actual text to be replaced by `suggestion`.
  If not provided it defaults to `ref`.
-/
def addExactSuggestion (ref : Syntax) (e : Expr)
    (origSpan? : Option Syntax := none) (addSubgoalsMsg := false) : TermElabM Unit := do
  addSuggestion ref (← addExactSuggestionCore addSubgoalsMsg e)
    (origSpan? := origSpan?)

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
  addSuggestion ref (← delabToRefinableSuggestion e) (origSpan? := origSpan?) (header := header)

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
  addSuggestions ref (← es.mapM delabToRefinableSuggestion)
    (origSpan? := origSpan?) (header := header)

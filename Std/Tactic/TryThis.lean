/-
Copyright (c) 2021 Gabriel Ebner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner, Mario Carneiro, Thomas Murrills
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

/--
This is a widget which is placed by `TryThis.addSuggestion` and `TryThis.addSuggestions`.

When placed by `addSuggestion`, it says `Try this: <replacement>`
where `<replacement>` is a link which will perform the replacement.

When placed by `addSuggestions`, it says:
```
Try these:
```
* `<replacement1>`
* `<replacement2>`
* `<replacement3>`
* ...

where `<replacement*>` is a link which will perform the replacement.
-/
@[widget] def tryThisWidget : Widget.UserWidgetDefinition where
  name := "Suggestion"
  javascript := "
import * as React from 'react';
import { EditorContext } from '@leanprover/infoview';
const e = React.createElement;
export default function(props) {
  const editorConnection = React.useContext(EditorContext)

  // Construct the style from the object corresponding to a given SuggestionStyle.
  function getStyle(style) {
    return !style ? {
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
        // Clip `t` to lie between 0 and 1. Interpolate between 0 and 120 (red and green).
        // Dim the lightness from 60% at the ends to 45% in the middle parabolically to at least
        // avoid total illegibility in light themes.
        style:{
          color:`hsl(${Math.round(Math.min(Math.max(style.value.t,0),1) * 120)} 95% ${
            60*(0.25 * Math.pow(2 * Math.min(Math.max(style.value.t,0),1) - 1,2) + 0.75)}%)`
        },
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

  // Construct the children of the HTML element for a given suggestion.
  function makeSuggestion({suggestion, preInfo, postInfo, style}) {

    function onClick() {
      editorConnection.api.applyEdit({
        changes: { [props.pos.uri]: [{ range: props.range, newText: suggestion }] }
      })
    }

    return [
      preInfo,
      e('span',
        {onClick, title: 'Apply suggestion', ...getStyle(style)},
        suggestion),
      postInfo
    ]
  }

  // Choose between an inline 'Try this'-like display and a list-based 'Try these'-like display.
  if (props.isInline) {
    return e('div', {className: 'ml1'},
      e('pre', {className: 'font-code pre-wrap'},
        props.header,
        makeSuggestion(props.suggestions[0]))
    )
  } else {
    function makeListElement(s) {
      return e('li', {className:'font-code pre-wrap'}, makeSuggestion(s))
    }
    const s = props.suggestions.map(makeListElement)
    return e('div', {className: 'ml1'},
      e('pre', {className: 'font-code pre-wrap'}, props.header),
      e('ul', {style:{paddingInlineStart:'20px'}}, s)
    )
  }
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
    let .ok range := props.getObjValAs? Lsp.Range "range" | panic! "bad type"
    let .ok suggestions := props.getObjVal? "suggestions" | panic! "bad type"
    let .ok suggestions := suggestions.getArr? | panic! "bad type"
    let some s := suggestions[0]? | return result
    let pushSuggestion (result : Array LazyCodeAction) (s : Json) (isPreferred? : Option Bool) := do
      let .ok newText := s.getObjValAs? String "suggestion" | panic! "bad type"
      result.push {
        eager.title := "Try this: " ++ newText
        eager.kind? := "quickfix"
        eager.isPreferred? := isPreferred?
        eager.edit? := some <| .ofTextEdit params.textDocument.uri { range, newText }
      }
    -- Only make the first option preferred
    let result ← pushSuggestion result s (isPreferred? := true)
    suggestions.foldlM (init := result) (start := 1) (pushSuggestion (isPreferred? := none))

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

/-- Delaborate `e` into syntax suitable for use by `refine`. -/
def delabToRefinableSyntax (e : Expr) : TermElabM Term :=
  return ⟨← replaceMVarsByUnderscores (← delab e)⟩

/-- The default maximum width of an ideal line in source code, 100 is the current convention. -/
def inputWidth : Nat := 100

/-- An option allowing the user to customize the ideal input width, this controls output format when
the output is intended to be copied back into a lean file -/
register_option format.inputWidth : Nat := {
  defValue := inputWidth
  descr := "ideal input width"
}

/-- Get the input width specified in the options -/
def getInputWidth (o : Options) : Nat := format.inputWidth.get o


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

/- Note that this is essentially `return (← s.pretty).prettyExtra w indent column`, but we
special-case strings to avoid converting them to `Format`s and back. -/
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
/- interpolates linearly from 0º to 120º with 95% saturation and lightness varying around 50% in
HSL space. -/
| value (t : Float) (showValueInHoverText := true)
deriving Inhabited, Repr, ToJson, FromJson

/-- Holds a `suggestion` for replacement, along with `preInfo` and `postInfo` strings to be printed
immediately before and after that suggestion, respectively. It also includes an optional
`MessageData` to represent the suggestion in logs; by default, this is `none`, and `suggestion` is
used. -/
structure Suggestion where
  /-- Text to be used as a replacement via a code action. -/
  suggestion : SuggestionText
  /-- Optional info to be printed immediately before replacement text in a widget. -/
  preInfo? : Option String := none
  /-- Optional info to be printed immediately after replacement text in a widget. -/
  postInfo? : Option String := none
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

/-- Converts a `Suggestion` to `Json` in `MetaM`. We need `MetaM` in order to pretty-print syntax.
-/
def Suggestion.toJsonM (s : Suggestion) (w : Nat := Format.defWidth) (indent column : Nat := 0)
    : MetaM Json := do
  let text ← s.suggestion.prettyExtra w indent column
  let mut json := [("suggestion", (text : Json))]
  if let some preInfo := s.preInfo? then json := ("preInfo", preInfo) :: json
  if let some postInfo := s.postInfo? then json := ("postInfo", postInfo) :: json
  if let some style := s.style? then json := ("style", toJson style) :: json
  return Json.mkObj json

/- If `messageData?` is specified, we use that; otherwise (by default), we use `toMessageData` of
the suggestion text. -/
instance : ToMessageData Suggestion where
  toMessageData s := s.messageData?.getD (toMessageData s.suggestion)

instance : Coe SuggestionText Suggestion where
  coe t := { suggestion := t }

/-- Delaborate `e` into a suggestion suitable for use by `refine`. -/
def delabToRefinableSuggestion (e : Expr) : TermElabM Suggestion :=
  return { suggestion := ← delabToRefinableSyntax e, messageData? := e }

/-! # Widget hooks -/

/-- Core of `addSuggestion` and `addSuggestions`. Whether we use an inline display for a single
element or a list display is controlled by `isInline`. -/
private def addSuggestionCore (ref : Syntax) (suggestions : Array Suggestion)
    (origSpan? : Option Syntax := none)
    (header : String) (isInline : Bool) : MetaM Unit := do
  if let some range := (origSpan?.getD ref).getRange? then
    let map ← getFileMap
    let (indent, column) := getIndentAndColumn map range
    let suggestions ← suggestions.mapM (·.toJsonM (indent := indent) (column := column))
    let stxRange := ref.getRange?.getD range
    let stxRange :=
      { start := map.lineStart (map.toPosition stxRange.start).line
        stop := map.lineStart ((map.toPosition stxRange.stop).line + 1) }
    let range := map.utf8RangeToLspRange range
    let json := Json.mkObj [
      ("suggestions", Json.arr suggestions),
      ("range", toJson range),
      ("header", header),
      ("isInline", toJson isInline)]
    Widget.saveWidgetInfo ``tryThisWidget json (.ofRange stxRange)


/-- Add a "try this" suggestion. This has three effects:

* An info diagnostic is displayed saying `Try this: <suggestion>`
* A widget is registered, saying `Try this: <suggestion>` with a link on `<suggestion>` to apply
  the suggestion
* A code action is added, which will apply the suggestion.

The parameters are:
* `ref`: the span of the info diagnostic
* `s`: a `Suggestion`, which contains
  * `suggestion`: the replacement text;
  * `preInfo?`: an optional string shown immediately after the replacement text in the widget
    message (only)
  * `postInfo?`: an optional string shown immediately after the replacement text in the widget
    message (only)
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
    (header : String := "Try this: ") : MetaM Unit := do
  logInfoAt ref m!"{header}{s}"
  addSuggestionCore ref ⟨[s]⟩ origSpan? header (isInline := true)

/-- Add a list of "try this" suggestions as a single "try these" suggestion. This has three effects:

* An info diagnostic is displayed saying `Try these: <list of suggestions>`
* A widget is registered, saying `Try these: <list of suggestions>` with a link on each
  `<suggestion>` to apply the suggestion
* A code action for each suggestion is added, which will apply the suggestion.

The parameters are:
* `ref`: the span of the info diagnostic
* `suggestions`: an array of `Suggestion`s, which each contain
  * `suggestion`: the replacement text;
  * `preInfo?`: an optional string shown immediately after the replacement text in the widget
    message (only)
  * `postInfo?`: an optional string shown immediately after the replacement text in the widget
    message (only)
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
    (header : String := "Try these:") : MetaM Unit := do
  if suggestions.isEmpty then throwErrorAt ref "no suggestions available"
  let msgs := suggestions.map toMessageData
  let msgs := msgs.foldl (init := MessageData.nil) (fun msg m => msg ++ m!"\n• " ++ m)
  logInfoAt ref m!"{header}{msgs}"
  addSuggestionCore ref suggestions origSpan? header (isInline := false)

private def addExactSuggestionCore (addSubgoalsMsg : Bool) (e : Expr) : TermElabM Suggestion := do
  let stx ← delabToRefinableSyntax e
  let mvars ← getMVars e
  let suggestion ← if mvars.isEmpty then `(tactic| exact $stx) else `(tactic| refine $stx)
  let messageData? := if mvars.isEmpty then m!"exact {e}" else m!"refine {e}"
  let postInfo? ← if !addSubgoalsMsg || mvars.isEmpty then pure none else
    let mut str := "\nRemaining subgoals:"
    for g in mvars do
      -- TODO: use a MessageData.ofExpr instead of rendering to string
      let e ← PrettyPrinter.ppExpr (← instantiateMVars (← g.getType))
      str := str ++ Format.pretty ("\n⊢ " ++ e)
    pure str
  pure { suggestion, postInfo?, messageData? }

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

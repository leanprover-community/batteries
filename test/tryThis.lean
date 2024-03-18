/-
Copyright (c) 2023 Thomas Murrills. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Murrills
-/
import Lean.Meta.Tactic.TryThis

open Lean.Meta.Tactic.TryThis

/-!
This test file demonstrates the `Try This:` widget and describes how certain examples should
look. Note that while the evaluations here shouldn't fail, they also aren't tests in the traditional
sense—CI has no way of inspecting the HTML output, and therefore no way of checking that the
output is styled correctly.

All clickables should dim on mouseover without changing color drastically.

Both widgets should provide a (list of) `Try this: rfl` code actions.
-/

/-! # Setup -/

open Lean Meta Elab Term Expr
/-- Add a suggestion. -/
elab "add_suggestion" s:term : tactic => unsafe do
  addSuggestion (← getRef) (← evalTerm Suggestion (.const ``Suggestion []) s)

/-- Add a suggestion with a header. -/
elab "add_suggestion" s:term "with_header" h:str : tactic => unsafe do
  addSuggestion (← getRef) (← evalTerm Suggestion (.const ``Suggestion []) s)
    (header := h.getString)

/-- Add a suggestion. -/
elab "add_suggestions" s:term : tactic => unsafe do
  let s ← evalTerm (Array Suggestion) (.app (.const ``Array [.zero]) (.const ``Suggestion [])) s
  addSuggestions (← getRef) s

/-- Add suggestions with a header. -/
elab "add_suggestions" s:term "with_header" h:str : tactic => unsafe do
  let s ← evalTerm (Array Suggestion) (.app (.const ``Array [.zero]) (.const ``Suggestion [])) s
  addSuggestions (← getRef) s (header := h.getString)

/-- Demo adding a suggestion. -/
macro "#demo1" s:term : command => `(example : True := by add_suggestion $s; trivial)

/-- Demo adding a suggestion with a header. -/
macro "#demo1" s:term "with_header" h:str : command => `(example : True := by
  add_suggestion $s with_header $h; trivial)

/-- Demo adding suggestions. -/
macro "#demo" s:term : command => `(example : True := by
  add_suggestions $s; trivial)

/-- Demo adding suggestions with a header. -/
macro "#demo" s:term "with_header" h:str : command => `(example : True := by
  add_suggestions $s with_header $h; trivial)

/-- A basic suggestion. -/
private def s : Suggestion := Unhygienic.run `(tactic| rfl)

/-! # Demos -/

/-- info: Try this: rfl -/
#guard_msgs in
-- `Try this: rfl` with `rfl` in text-link color.
#demo1 s

/--
info: Try these:
• rfl
• rfl
• rfl
• rfl
-/
#guard_msgs in
/-
```
Try these:
• rfl
• rfl
• rfl
• rfl
```
with `rfl` in text-link color.
-/
#demo #[s,s,s,s]

/--
info: Try these:
• rfl
• rfl
• rfl
• rfl
• rfl
• rfl
• rfl
-/
#guard_msgs in
/-
```
Try these:
• rfl -- red
• rfl -- red-orange
• rfl -- orange
• rfl -- yellow
• rfl -- yellow-green
• rfl -- light green
• rfl -- green
```
-/
#demo #[0.0, 1/6, 2/6, 3/6, 4/6, 5/6, 1.0].map fun t => {s with style? := some <| .value t}

/-- info: Try this: rfl -/
#guard_msgs in
-- `Try this: rfl` -- error color with error squiggle
#demo1 {s with style? := some .error}

/-- info: Try this: rfl -/
#guard_msgs in
-- `Try this: rfl` -- error color, no squiggle
#demo1 {s with style? := some <| .error (decorated := false)}

/-- info: Try this: rfl -/
#guard_msgs in
-- `Try this: rfl` -- gold color with warning squiggle
#demo1 {s with style? := some .warning}

/-- info: Try this: rfl -/
#guard_msgs in
-- `Try this: rfl` -- gold color with no squiggle
#demo1 {s with style? := some <| .warning (decorated := false)}

/-- info: Try this: rfl -/
#guard_msgs in
-- `Try this: rfl` -- Lean green
#demo1 {s with style? := some .success}

/-- info: Try this: rfl -/
#guard_msgs in
-- `Try this: rfl` -- styled like a goal hypothesis
#demo1 {s with style? := some .asHypothesis}

/-- info: Try this: rfl -/
#guard_msgs in
-- `Try this: rfl` -- styled like an inaccessible goal hypothesis
#demo1 {s with style? := some .asInaccessible}

/-- info: Try this: rfl -/
#guard_msgs in
-- `Try this: Starfleet`
#demo1 {s with preInfo? := "Sta", postInfo? := "eet"}

/-- info: Try this: a secret message -/
#guard_msgs in
-- `Try this: rfl`
#demo1 {s with messageData? := m!"a secret message"}

/--
info: Try these:
• a secret message
• another secret message
-/
#guard_msgs in
/-
```
Try these:
• rfl
• rfl
```
-/
#demo #[
  {s with messageData? := m!"a secret message"},
  {s with messageData? := m!"another secret message"}
]

/-- info: Our only hope is rfl -/
#guard_msgs in
#demo1 s with_header "Our only hope is "

/--
info: We've got everything here! Such as:
• rfl
• rfl
• rfl
• rfl
-/
#guard_msgs in
#demo #[s,s,s,s] with_header "We've got everything here! Such as:"

/--
info: Grab bag:
• not a tactic
• This
• rfl
• link-styled
• this
-/
#guard_msgs in
#demo #[
  {s with
    suggestion := "not a tactic",
    preInfo? := "This is ",
    postInfo? := ".",
    style? := some .error},
  {s with
    suggestion := "This",
    postInfo? := " could be a tactic--but watch out!",
    style? := some .warning},
  {s with
    postInfo? := ". Finally, a tactic that just works.",
    style? := some .success},
  {s with
    preInfo? := "I'm just "
    suggestion := "link-styled",
    postInfo? := "."},
  {s with
    preInfo? := "On a scale of 0 to 1, I'd put ",
    suggestion := "this",
    postInfo? := " at 0.166667.",
    style? := some (.value (1/6))}
] with_header "Grab bag:"

/-- error: no suggestions available -/
#guard_msgs in
#demo #[]

/- The messages and suggestion should still read `Try this: rfl`, but the text in the lightbulb
menu should read "Consider rfl, please" -/
/-- info: Try this: rfl -/
#guard_msgs in
#demo1 { s with toCodeActionTitle? := fun text => "Consider " ++ text ++ ", please" }

/-- Add suggestions with a default code action title prefix. -/
elab "add_suggestions" s:term "with_code_action_prefix" h:str : tactic => unsafe do
  let s ← evalTerm (Array Suggestion) (.app (.const ``Array [.zero]) (.const ``Suggestion [])) s
  addSuggestions (← getRef) s (codeActionPrefix? := h.getString)

/-- Demo adding suggestions with a header. -/
macro "#demo" s:term "with_code_action_prefix" h:str : command => `(example : True := by
  add_suggestions $s with_code_action_prefix $h; trivial)

/- The messages and suggestions should still read `Try these: ...`, but the text in the lightbulb
menu should read "Maybe use: rfl"; "Maybe use: rfl"; "Also consider rfl, please!" -/
/--
info: Try these:
• rfl
• rfl
• rfl
-/
#guard_msgs in
#demo #[
  s,
  s,
  { s with toCodeActionTitle? := fun text => "Also consider " ++ text ++ ", please!" }
] with_code_action_prefix "Maybe use: "

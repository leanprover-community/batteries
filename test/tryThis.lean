/-
Copyright (c) 2023 Thomas Murrills. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Murrills
-/
import Std.Tactic.TryThis
import Std.Util.TermUnsafe
import Std.Tactic.GuardMsgs

open Std.Tactic.TryThis

/-! This test file demonstrates the `Try This:` widget and describes how certain examples should
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
elab "add_suggestion" s:term "with_header" h:term : tactic => unsafe do
  addSuggestion (← getRef) (← evalTerm Suggestion (.const ``Suggestion []) s)
    (header := ← evalTerm String (.const ``String []) h)

/-- Add a suggestion. -/
elab "add_suggestions" s:term : tactic => unsafe do
  let s ← evalTerm (Array Suggestion) (.app (.const ``Array [.zero]) (.const ``Suggestion [])) s
  addSuggestions (← getRef) s

/-- Add suggestions with a header. -/
elab "add_suggestions" s:term "with_header" h:term : tactic => unsafe do
  let s ← evalTerm (Array Suggestion) (.app (.const ``Array [.zero]) (.const ``Suggestion [])) s
  addSuggestions (← getRef) s (header := ← evalTerm String (.const ``String []) h)

/-- Demo adding a suggestion. -/
macro "#demo1" s:term : command => `(example : True := by add_suggestion $s; trivial)
/-- Demo adding a suggestion with a header. -/
macro "#demo1" s:term "with_header" h:term : command => `(example : True := by
  add_suggestion $s with_header $h; trivial)
/-- Demo adding suggestions. -/
macro "#demo" s:term : command => `(example : True := by
  add_suggestions $s; trivial)
/-- Demo adding suggestions with a header. -/
macro "#demo" s:term "with_header" h:term : command => `(example : True := by
  add_suggestions $s with_header $h; trivial)

/-- The syntax you typically get from ``←`(tactic|rfl)`` -/
private def demoSyntax : TSyntax `tactic := {
  raw := Lean.Syntax.node
    (Lean.SourceInfo.none)
    `Lean.Parser.Tactic.tacticRfl
    #[Lean.Syntax.atom (Lean.SourceInfo.none) "rfl"] }

/-- A basic suggestion. -/
private def s : Suggestion := demoSyntax

/-! # Demos -/

-- `Try this: rfl` with `rfl` in text-link color.
#demo1 s

/-
```
Try these:
• rfl
• rfl
• rfl
• rfl
```
with `rfl` in text-link color/ -/
#demo #[s,s,s,s]

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

-- `Try this: rfl` -- error color with error squiggle
#demo1 {s with style? := some .error}

-- `Try this: rfl` -- error color, no squiggle
#demo1 {s with style? := some <| .error (decorated := false)}

-- `Try this: rfl` -- gold color with warning squiggle
#demo1 {s with style? := some .warning}

-- `Try this: rfl` -- gold color with no squiggle
#demo1 {s with style? := some <| .warning (decorated := false)}

-- `Try this: rfl` -- Lean green
#demo1 {s with style? := some .success}

-- `Try this: rfl` -- styled like a goal hypothesis
#demo1 {s with style? := some .asHypothesis}

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
-- `Try this: rfl`
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

/-
Copyright (c) 2023 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Lean.Elab.BuiltinTerm
import Lean.Elab.BuiltinNotation
import Std.Lean.Name
import Std.CodeAction.Hole.Attr

/-!
# Initial setup for hole code actions

This declares a code action provider that calls all `@[hole_code_action]` definitions
on each occurrence of a hole (`_`, `?_` or `sorry`).

(This is in a separate file from `Std.CodeAction.Hole.Attr` so that the server does not attempt
to use this code action provider when browsing the `Std.CodeAction.Hole.Attr` file itself.)
-/
namespace Std.CodeAction

open Lean Elab.Term Server RequestM

/--
A code action which calls all `@[hole_code_action]` code actions on each hole
(`?_`, `_`, or `sorry`).
-/
@[code_action_provider] def holeCodeActionProvider : CodeActionProvider := fun params snap => do
  let doc ← readDoc
  let startPos := doc.meta.text.lspPosToUtf8Pos params.range.start
  let endPos := doc.meta.text.lspPosToUtf8Pos params.range.end
  have holes := snap.infoTree.foldInfo (init := #[]) fun ctx info result => Id.run do
    let .ofTermInfo info := info | result
    unless [``elabHole, ``elabSyntheticHole, ``elabSorry].contains info.elaborator do
      return result
    let (some head, some tail) := (info.stx.getPos? true, info.stx.getTailPos? true) | result
    unless head ≤ endPos && startPos ≤ tail do return result
    result.push (ctx, info)
  let #[(ctx, info)] := holes | return #[]
  (holeCodeActionExt.getState snap.env).2.concatMapM (· params snap ctx info)

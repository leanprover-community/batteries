/-
Copyright (c) 2023 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Lean.Server.CodeActions
import Batteries.CodeAction.Basic

/-!
# Code action for @[deprecated] replacements

This is an opt-in mechanism for making machine-applicable `@[deprecated]` definitions. When enabled
(by setting the `machineApplicableDeprecated` tag attribute), a code action will be triggered
whenever the deprecation lint also fires, allowing the user to replace the usage of the deprecated
constant.
-/
namespace Std
open Lean Elab Server Lsp RequestM

/-- An environment extension for identifying `@[deprecated]` definitions which can be auto-fixed -/
initialize machineApplicableDeprecated : TagDeclarationExtension ← mkTagDeclarationExtension

namespace CodeAction

/-- A code action which applies replacements for `@[deprecated]` definitions. -/
@[code_action_provider]
def deprecatedCodeActionProvider : CodeActionProvider := fun params snap => do
  let mut i := 0
  let doc ← readDoc
  let mut msgs := #[]
  for m in snap.msgLog.toList do
    if m.data.isDeprecationWarning then
      if h : _ then
        msgs := msgs.push (snap.cmdState.messages.toList[i]'h)
    i := i + 1
  if msgs.isEmpty then return #[]
  let start := doc.meta.text.lspPosToUtf8Pos params.range.start
  let stop := doc.meta.text.lspPosToUtf8Pos params.range.end
  for msg in msgs do
    let some endPos := msg.endPos | continue
    let pos := doc.meta.text.ofPosition msg.pos
    let endPos' := doc.meta.text.ofPosition endPos
    unless start ≤ endPos' && pos ≤ stop do continue
    let some (ctx, .node (.ofTermInfo info@{ expr := .const c .., ..}) _) :=
      findInfoTree? identKind ⟨pos, endPos'⟩ none snap.infoTree fun _ i =>
        (i matches .ofTermInfo { elaborator := .anonymous, expr := .const .., ..})
      | continue
    unless machineApplicableDeprecated.isTagged snap.cmdState.env c do continue
    let some c' := Linter.getDeprecatedNewName snap.cmdState.env c | continue
    let eager : CodeAction := {
      title := s!"Replace {c} with {c'}"
      kind? := "quickfix"
      isPreferred? := true
    }
    return #[{
      eager
      lazy? := some do
        let c' ← info.runMetaM ctx (unresolveNameGlobal c')
        let pos := doc.meta.text.leanPosToLspPos msg.pos
        let endPos' := doc.meta.text.leanPosToLspPos endPos
        pure { eager with
          edit? := some <| .ofTextEdit doc.versionedIdentifier {
            range := ⟨pos, endPos'⟩
            newText := toString c'
          }
        }
    }]
  return #[]

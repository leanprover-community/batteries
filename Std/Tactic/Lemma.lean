/-
Copyright (c) 2024 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Damiano Testa
-/
import Std.Tactic.TryThis

/-!
#  Control for `lemma` command

The `lemma` command exists in `Mathlib`, but not in `Std`.

This file enforces the convention by introducing a code-action
to replace `lemma` by `theorem`.
-/

namespace Std.Tactic.Lemma

open Lean Elab.Command

/-- `lemma` is not supported, please use `theorem` instead -/
syntax (name := lemmaCmd) declModifiers
  group("lemma " declId ppIndent(declSig) declVal) : command

/-- Elaborator for the `lemma` command, with a boolean flag to control
whether the command emits a warning and code action
instructing the user to use `theorem` instead.-/
def elabLemma' (allow : Bool) : CommandElab := fun stx => do
  unless allow do
    let lemmaStx := stx[1][0]
    Elab.Command.liftTermElabM <|
      Std.Tactic.TryThis.addSuggestion lemmaStx { suggestion := "theorem" }
    logErrorAt lemmaStx
      s!"`lemma` is not supported, please use `theorem` instead.\n\
      note: Mathlib defines a `lemma` command, did you mean to `import Mathlib.Tactic.Basic`?"
  let out ← Elab.liftMacroM <| do
    let stx := stx.modifyArg 1 fun stx =>
      let stx := stx.modifyArg 0 (mkAtomFrom · "theorem" (canonical := true))
      stx.setKind ``Parser.Command.theorem
    pure <| stx.setKind ``Parser.Command.declaration
  Elab.Command.elabCommand out

@[inherit_doc lemmaCmd, command_elab «lemmaCmd»] def elabLemma : CommandElab := elabLemma' false

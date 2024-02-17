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

/-- Enables the use of `lemma` as a synonym for `theorem` -/
register_option lang.lemmaCmd : Bool := {
  defValue := false
  descr := "enable the use of the `lemma` command as a synonym for `theorem`"
}

/-- Check whether `lang.lemmaCmd` option is enabled -/
def checkLangLemmaCmd (o : Options) : Bool := o.get `lang.lemmaCmd lang.lemmaCmd.defValue

/-- `lemma` is not supported, please use `theorem` instead -/
syntax (name := lemmaCmd) declModifiers
  group("lemma " declId ppIndent(declSig) declVal) : command

/-- Elaborator for the `lemma` command, if the option `lang.lemmaCmd` is false the command
emits a warning and code action instructing the user to use `theorem` instead.-/
@[command_elab «lemmaCmd»] def elabLemma : CommandElab := fun stx => do
  unless checkLangLemmaCmd (← getOptions) do
    let lemmaStx := stx[1][0]
    Elab.Command.liftTermElabM <|
      Std.Tactic.TryThis.addSuggestion lemmaStx { suggestion := "theorem" }
    logErrorAt lemmaStx
      "`lemma` is not supported, please use `theorem` instead.\n\
      Use `set_option lang.lemmaCmd true` to enable the use of the `lemma` command"
  let out ← Elab.liftMacroM <| do
    let stx := stx.modifyArg 1 fun stx =>
      let stx := stx.modifyArg 0 (mkAtomFrom · "theorem" (canonical := true))
      stx.setKind ``Parser.Command.theorem
    pure <| stx.setKind ``Parser.Command.declaration
  Elab.Command.elabCommand out

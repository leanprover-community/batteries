/-
Copyright (c) 2021 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/

namespace Lean.Parser.Tactic

-- syntax simpArg := simpStar <|> simpErase <|> simpLemma
/--
A `simpArg` is either a `*`, `-lemma` or a simp lemma specification
(which includes the `↑` `↓` `←` specifications for pre, post, reverse rewriting).
-/
def simpArg := simpStar.binary `orelse (simpErase.binary `orelse simpLemma)

/-- A simp args list is a list of `simpArg`. This is the main argument to `simp`. -/
syntax simpArgs := " [" simpArg,* "] "

/-- Extract the arguments from a `simpArgs` syntax as an array of syntaxes -/
def getSimpArgs? : Syntax → Option (Array Syntax)
  | `(simpArgs| [$args,*]) => pure args.getElems
  | _ => none

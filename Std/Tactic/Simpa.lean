/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Paulino, Gabriel Ebner, Mario Carneiro
-/
import Lean.Elab.Tactic.ElabTerm
import Std.Lean.Expr
import Std.Lean.Parser

namespace Std.Tactic

open Lean Parser.Tactic Elab.Tactic

/-- The arguments to the `simpa` family tactics. -/
syntax simpaArgsRest := (config)? (discharger)? &" only "? (simpArgs)? (" using " term)?

/--
This is a "finishing" tactic modification of `simp`. It has two forms.

* `simpa [rules, ⋯] using e` will simplify the goal and the type of
  `e` using `rules`, then try to close the goal using `e`.

  Simplifying the type of `e` makes it more likely to match the goal
  (which has also been simplified). This construction also tends to be
  more robust under changes to the simp lemma set.

* `simpa [rules, ⋯]` will simplify the goal and the type of a
  hypothesis `this` if present in the context, then try to close the goal using
  the `assumption` tactic.

#TODO: implement `?`
-/
syntax (name := simpa) "simpa" "?"? "!"? simpaArgsRest : tactic
@[inherit_doc simpa] macro "simpa!" rest:simpaArgsRest : tactic =>
  `(tactic| simpa ! $rest:simpaArgsRest)
@[inherit_doc simpa] macro "simpa?" rest:simpaArgsRest : tactic =>
  `(tactic| simpa ? $rest:simpaArgsRest)
@[inherit_doc simpa] macro "simpa?!" rest:simpaArgsRest : tactic =>
  `(tactic| simpa ?! $rest:simpaArgsRest)

elab_rules : tactic
| `(tactic| simpa $[?%$squeeze]? $[!%$unfold]? $(cfg)? $(disch)? $[only%$only]?
      $[[$args,*]]? $[using $usingArg]?) => Elab.Tactic.focus do
  if squeeze.isSome then throwError "TODO: lemma tracing"
  let simpTac loc :=
    if unfold.isSome then
      `(tactic| try simp! $(cfg)? $(disch)? $[only%$only]? $[[$args,*]]? $(loc)?)
    else
      `(tactic| try simp $(cfg)? $(disch)? $[only%$only]? $[[$args,*]]? $(loc)?)
  evalTactic <|← simpTac none
  let g ← try getMainGoal catch _ => throwError "try 'simp' instead of 'simpa'"
  if let some e := usingArg then
    g.withContext do
      let e ← elabTerm e none
      evalTactic <|← `(tactic| have' h := $(← e.toSyntax))
      evalTactic <|← simpTac (← `(location| at h))
      if ← try getMainGoal *> pure true catch _ => pure false then
        evalTactic <|← `(tactic| exact h)
      else if e.isFVar then throwError "try 'simp at {e}' instead of 'simpa using {e}'"
  else
    evalTactic <|← simpTac (← `(location| at this))
    _ ← try getMainGoal catch _ => throwError "try 'simp at this' instead of 'simpa'"
    evalTactic <|← `(tactic| assumption)

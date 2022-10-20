/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Paulino, Gabriel Ebner, Mario Carneiro
-/
import Lean.Elab.ElabRules
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
| `(tactic| simpa $[?%$squeeze]? $[!%$unfold]? $[$cfg:config]? $[$disch:discharger]? $[only%$only]?
      $[[$args,*]]? $[using $usingArg]?) => do
  if squeeze.isSome then throwError "TODO: lemma tracing"
  let nGoals := (← getUnsolvedGoals).length
  evalTactic <|← `(tactic| simp $(cfg)? $(disch)? $[only%$only]? $[[$[$args],*]]?)
  if (← getUnsolvedGoals).length < nGoals then throwError "try 'simp' instead of 'simpa'"
  let simpTac loc :=
    if unfold.isSome then
      `(tactic| try simp! $(cfg)? $(disch)? $[only%$only]? $[[$[$args],*]]? $loc:location)
    else
      `(tactic| try simp $(cfg)? $(disch)? $[only%$only]? $[[$[$args],*]]? $loc:location)
  match usingArg with
  | none   =>
    evalTactic <|← simpTac (← `(location| at this))
    evalTactic <|← `(tactic| assumption)
  | some e =>
    evalTactic <|← `(tactic| have' h := $e)
    evalTactic <|← simpTac (← `(location| at h))
    evalTactic <|← `(tactic| exact h)

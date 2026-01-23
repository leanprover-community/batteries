/-
Copyright (c) 2021 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public meta import Lean.DocString
public meta import Lean.Elab.Tactic.Basic

public meta section

/-!
Deprecation warnings for `match ⋯ with.`, `fun.`, `λ.`, and `intro.`.
-/
namespace Batteries.Tactic
open Lean Elab Term Tactic Parser.Term

/--
The syntax `match ⋯ with.` has been deprecated in favor of `nomatch ⋯`.

Both now support multiple discriminants.
-/
elab (name := matchWithDot) (priority := low)
    tk:"match " t:term,* " with" "." : term <= expectedType? => do
  logWarningAt tk (← findDocString? (← getEnv) ``matchWithDot).get!
  elabTerm (← `(nomatch%$tk $[$t],*)) expectedType?

/-- The syntax `fun.` has been deprecated in favor of `nofun`. -/
elab (name := funDot) (priority := low) tk:"fun" "." : term <= expectedType? => do
  logWarningAt tk (← findDocString? (← getEnv) ``funDot).get!
  elabTerm (← `(nofun)) expectedType?

/-- The syntax `λ.` has been deprecated in favor of `nofun`. -/
elab (name := lambdaDot) (priority := low) tk:"fun" "." : term <= expectedType? => do
  logWarningAt tk (← findDocString? (← getEnv) ``lambdaDot).get!
  elabTerm (← `(nofun)) expectedType?

@[inherit_doc matchWithDot]
macro (priority := low) "match " discrs:term,* " with" "." : tactic =>
  `(tactic| exact match $discrs,* with.)

/--
The syntax `intro.` is deprecated in favor of `nofun`.
-/
elab (name := introDot) tk:"intro" "." : tactic => do
  logWarningAt tk (← findDocString? (← getEnv) ``introDot).get!
  evalTactic (← `(tactic| nofun))

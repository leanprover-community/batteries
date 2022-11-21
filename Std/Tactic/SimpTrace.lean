/-
Copyright (c) 2022 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Lean.Elab.ElabRules
import Std.Lean.Parser

/-!
# `simp?` tactic

The `simp?` tactic is a simple wrapper around the simp with trace behavior implemented in core.
-/
namespace Std.Tactic
open Lean Elab Parser Tactic

/-- The common arguments of `simp?` and `simp?!`. -/
syntax simpTraceArgsRest := (config)? (discharger)? (&" only")? (simpArgs)? (ppSpace location)?

/--
`simp?` takes the same arguments as `simp`, but reports an equivalent call to `simp only`
that would be sufficient to close the goal. This is useful for reducing the size of the simp
set in a local invocation to speed up processing.
```
example (x : Nat) : (if True then x + 2 else 3) = x + 2 := by
  simp? -- prints "Try this: simp only [ite_true]"
```

This command can also be used in `simp_all` and `dsimp`.
-/
syntax (name := simpTrace) "simp?" "!"? simpTraceArgsRest : tactic

@[inherit_doc simpTrace]
macro tk:"simp?!" rest:simpTraceArgsRest : tactic => `(tactic| simp?%$tk ! $rest)

macro_rules
  | `(tactic| simp?%$tk $(config)? $(discharger)? $[only%$o]? $[[$args,*]]? $(loc)?) =>
    `(tactic| set_option tactic.simp.trace true in
      simp%$tk $(config)? $(discharger)? $[only%$o]? $[[$args,*]]? $(loc)?)
  | `(tactic| simp?%$tk ! $(config)? $(discharger)? $[only%$o]? $[[$args,*]]? $(loc)?) =>
    `(tactic| set_option tactic.simp.trace true in
      simp!%$tk $(config)? $(discharger)? $[only%$o]? $[[$args,*]]? $(loc)?)

/-- The common arguments of `simp_all?` and `simp_all?!`. -/
syntax simpAllTraceArgsRest := (config)? (discharger)? (&" only")? (dsimpArgs)?

@[inherit_doc simpTrace]
syntax (name := simpAllTrace) "simp_all?" "!"? simpAllTraceArgsRest : tactic

@[inherit_doc simpTrace]
macro tk:"simp_all?!" rest:simpAllTraceArgsRest : tactic => `(tactic| simp_all?%$tk ! $rest)

macro_rules
  | `(tactic| simp_all?%$tk $(config)? $(discharger)? $[only%$o]? $[[$args,*]]?) =>
    `(tactic| set_option tactic.simp.trace true in
      simp_all%$tk $(config)? $(discharger)? $[only%$o]? $[[$args,*]]?)
  | `(tactic| simp_all?%$tk ! $(config)? $(discharger)? $[only%$o]? $[[$args,*]]?) =>
    `(tactic| set_option tactic.simp.trace true in
      simp_all!%$tk $(config)? $(discharger)? $[only%$o]? $[[$args,*]]?)

/-- The common arguments of `dsimp?` and `dsimp?!`. -/
syntax dsimpTraceArgsRest := (config)? (&" only")? (dsimpArgs)? (ppSpace location)?

@[inherit_doc simpTrace]
syntax (name := dsimpTrace) "dsimp?" "!"? dsimpTraceArgsRest : tactic

@[inherit_doc simpTrace]
macro tk:"dsimp?!" rest:dsimpTraceArgsRest : tactic => `(tactic| dsimp?%$tk ! $rest)

macro_rules
  | `(tactic| dsimp?%$tk $(config)? $[only%$o]? $[[$args,*]]? $(loc)?) =>
    `(tactic| set_option tactic.simp.trace true in
      dsimp%$tk $(config)? $[only%$o]? $[[$args,*]]? $(loc)?)
  | `(tactic| dsimp?%$tk ! $(config)? $[only%$o]? $[[$args,*]]? $(loc)?) =>
    `(tactic| set_option tactic.simp.trace true in
      dsimp!%$tk $(config)? $[only%$o]? $[[$args,*]]? $(loc)?)

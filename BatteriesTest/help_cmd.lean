import Batteries.Tactic.HelpCmd

/-! The `#help` command

The `#help` command family currently contains these subcommands:

* `#help attr` / `#help attribute`
* `#help cat`
* `#help cats`
* `#help command` (abbrev for `#help cat command`)
* `#help conv` (abbrev for `#help cat conv`)
* `#help option`
* `#help tactic` (abbrev for `#help cat tactic`)
* `#help term` (abbrev for `#help cat term`)

All forms take an optional identifier prefix to narrow the search. The `#help cat` command has a
variant `#help cat+` that displays additional information, similarly for commands derived from
`#help cat`.

WARNING: Some of these tests will need occasional updates when new features are added and even when
some documentation is edited. This type of break will be unexpected but the fix will not be
unexpected! Just update the guard text to match the output after your addition.
-/

/-! `#help attr` -/

-- this is a long and constantly updated listing, we don't check the output
#guard_msgs(error, drop info) in
#help attr

/--
error: no attributes start with foobarbaz
-/
#guard_msgs in
#help attr foobarbaz

/--
info:
[inline]: mark definition to be inlined

[inline_if_reduce]: mark definition to be inlined when resultant term after reduction is not a
`cases_on` application
-/
#guard_msgs in
#help attr inl

/-! `#help cat` -/

-- this is a long and constantly updated listing, we don't check the output
#guard_msgs(error, drop info) in
#help cat term

/--
error: foobarbaz is not a syntax category
-/
#guard_msgs in
#help cat foobarbaz

/--
info:
syntax "("... [«prec(_)»]
  Parentheses are used for grouping precedence expressions.

syntax "+"... [Lean.Parser.Syntax.addPrec]
  Addition of precedences. This is normally used only for offsetting, e.g. `max + 1`.

syntax "-"... [Lean.Parser.Syntax.subPrec]
  Subtraction of precedences. This is normally used only for offsetting, e.g. `max - 1`.

syntax "arg"... [precArg]
  Precedence used for application arguments (`do`, `by`, ...).

syntax "lead"... [precLead]
  Precedence used for terms not supposed to be used as arguments (`let`, `have`, ...).

syntax "max"... [precMax]
  Maximum precedence used in term parsers, in particular for terms in
  function position (`ident`, `paren`, ...)

syntax "min"... [precMin]
  Minimum precedence used in term parsers.

syntax "min1"... [precMin1]
  `(min+1)` (we can only write `min+1` after `Meta.lean`)

syntax ... [Lean.Parser.Syntax.numPrec]
-/
#guard_msgs in
#help cat prec

/--
info:
syntax "("... [«prec(_)»]
  Parentheses are used for grouping precedence expressions.
+ macro «_aux_Init_Notation___macroRules_prec(_)_1»
  Parentheses are used for grouping precedence expressions.

syntax "+"... [Lean.Parser.Syntax.addPrec]
  Addition of precedences. This is normally used only for offsetting, e.g. `max + 1`.
+ macro Lean._aux_Init_Meta___macroRules_Lean_Parser_Syntax_addPrec_1

syntax "-"... [Lean.Parser.Syntax.subPrec]
  Subtraction of precedences. This is normally used only for offsetting, e.g. `max - 1`.
+ macro Lean._aux_Init_Meta___macroRules_Lean_Parser_Syntax_subPrec_1

syntax "arg"... [precArg]
  Precedence used for application arguments (`do`, `by`, ...).
+ macro _aux_Init_Notation___macroRules_precArg_1
  Precedence used for application arguments (`do`, `by`, ...).

syntax "lead"... [precLead]
  Precedence used for terms not supposed to be used as arguments (`let`, `have`, ...).
+ macro _aux_Init_Notation___macroRules_precLead_1
  Precedence used for terms not supposed to be used as arguments (`let`, `have`, ...).

syntax "max"... [precMax]
  Maximum precedence used in term parsers, in particular for terms in
  function position (`ident`, `paren`, ...)
+ macro _aux_Init_Notation___macroRules_precMax_1
  Maximum precedence used in term parsers, in particular for terms in
  function position (`ident`, `paren`, ...)

syntax "min"... [precMin]
  Minimum precedence used in term parsers.
+ macro _aux_Init_Notation___macroRules_precMin_1
  Minimum precedence used in term parsers.

syntax "min1"... [precMin1]
  `(min+1)` (we can only write `min+1` after `Meta.lean`)
+ macro _aux_Init_Notation___macroRules_precMin1_1
  `(min+1)` (we can only write `min+1` after `Meta.lean`)

syntax ... [Lean.Parser.Syntax.numPrec]
-/
#guard_msgs in
#help cat+ prec

/-! `#help cats` -/

-- this is a long and constantly updated listing, we don't check the output
#guard_msgs(error, drop info) in
#help cats

/--
error: no syntax categories start with foobarbaz
-/
#guard_msgs in
#help cats foobarbaz

/--
info: category prec [Lean.Parser.Category.prec]
  `prec` is a builtin syntax category for precedences. A precedence is a value
  that expresses how tightly a piece of syntax binds: for example `1 + 2 * 3` is
  parsed as `1 + (2 * 3)` because `*` has a higher precedence than `+`.
  Higher numbers denote higher precedence.
  In addition to literals like `37`, there are some special named precedence levels:
  * `arg` for the precedence of function arguments
  * `max` for the highest precedence used in term parsers (not actually the maximum possible value)
  * `lead` for the precedence of terms not supposed to be used as arguments
  and you can also add and subtract precedences.

category prio [Lean.Parser.Category.prio]
  `prio` is a builtin syntax category for priorities.
  Priorities are used in many different attributes.
  Higher numbers denote higher priority, and for example typeclass search will
  try high priority instances before low priority.
  In addition to literals like `37`, you can also use `low`, `mid`, `high`, as well as
  add and subtract priorities.
-/
#guard_msgs in
#help cats pr

/-! `#help command` -/

-- this is a long and constantly updated listing, we don't check the output
#guard_msgs(error, drop info) in
#help command

/--
error: no command declarations start with foobarbaz
-/
#guard_msgs in
#help command foobarbaz

/--
info: syntax "#eval"... [Lean.Parser.Command.eval]
  `#eval e` evaluates the expression `e` by compiling and evaluating it.
  ⏎
  * The command attempts to use `ToExpr`, `Repr`, or `ToString` instances to print the result.
  * If `e` is a monadic value of type `m ty`, then the command tries to adapt the monad `m`
    to one of the monads that `#eval` supports, which include `IO`, `CoreM`, `MetaM`, `TermElabM`, and `CommandElabM`.
    Users can define `MonadEval` instances to extend the list of supported monads.
  ⏎
  The `#eval` command gracefully degrades in capability depending on what is imported.
  Importing the `Lean.Elab.Command` module provides full capabilities.
  ⏎
  Due to unsoundness, `#eval` refuses to evaluate expressions that depend on `sorry`, even indirectly,
  since the presence of `sorry` can lead to runtime instability and crashes.
  This check can be overridden with the `#eval! e` command.
  ⏎
  Options:
  * If `eval.pp` is true (default: true) then tries to use `ToExpr` instances to make use of the
    usual pretty printer. Otherwise, only tries using `Repr` and `ToString` instances.
  * If `eval.type` is true (default: false) then pretty prints the type of the evaluated value.
  * If `eval.derive.repr` is true (default: true) then attempts to auto-derive a `Repr` instance
    when there is no other way to print the result.
  ⏎
  See also: `#reduce e` for evaluation by term reduction.

syntax "#eval!"... [Lean.Parser.Command.evalBang]
  `#eval e` evaluates the expression `e` by compiling and evaluating it.
  ⏎
  * The command attempts to use `ToExpr`, `Repr`, or `ToString` instances to print the result.
  * If `e` is a monadic value of type `m ty`, then the command tries to adapt the monad `m`
    to one of the monads that `#eval` supports, which include `IO`, `CoreM`, `MetaM`, `TermElabM`, and `CommandElabM`.
    Users can define `MonadEval` instances to extend the list of supported monads.
  ⏎
  The `#eval` command gracefully degrades in capability depending on what is imported.
  Importing the `Lean.Elab.Command` module provides full capabilities.
  ⏎
  Due to unsoundness, `#eval` refuses to evaluate expressions that depend on `sorry`, even indirectly,
  since the presence of `sorry` can lead to runtime instability and crashes.
  This check can be overridden with the `#eval! e` command.
  ⏎
  Options:
  * If `eval.pp` is true (default: true) then tries to use `ToExpr` instances to make use of the
    usual pretty printer. Otherwise, only tries using `Repr` and `ToString` instances.
  * If `eval.type` is true (default: false) then pretty prints the type of the evaluated value.
  * If `eval.derive.repr` is true (default: true) then attempts to auto-derive a `Repr` instance
    when there is no other way to print the result.
  ⏎
  See also: `#reduce e` for evaluation by term reduction.  syntax "#exit"... [Lean.Parser.Command.exit]
-/
#guard_msgs in
#help command "#e"

/--
info: syntax "#eval"... [Lean.Parser.Command.eval]
  `#eval e` evaluates the expression `e` by compiling and evaluating it.
  ⏎
  * The command attempts to use `ToExpr`, `Repr`, or `ToString` instances to print the result.
  * If `e` is a monadic value of type `m ty`, then the command tries to adapt the monad `m`
    to one of the monads that `#eval` supports, which include `IO`, `CoreM`, `MetaM`, `TermElabM`, and `CommandElabM`.
    Users can define `MonadEval` instances to extend the list of supported monads.
  ⏎
  The `#eval` command gracefully degrades in capability depending on what is imported.
  Importing the `Lean.Elab.Command` module provides full capabilities.
  ⏎
  Due to unsoundness, `#eval` refuses to evaluate expressions that depend on `sorry`, even indirectly,
  since the presence of `sorry` can lead to runtime instability and crashes.
  This check can be overridden with the `#eval! e` command.
  ⏎
  Options:
  * If `eval.pp` is true (default: true) then tries to use `ToExpr` instances to make use of the
    usual pretty printer. Otherwise, only tries using `Repr` and `ToString` instances.
  * If `eval.type` is true (default: false) then pretty prints the type of the evaluated value.
  * If `eval.derive.repr` is true (default: true) then attempts to auto-derive a `Repr` instance
    when there is no other way to print the result.
  ⏎
  See also: `#reduce e` for evaluation by term reduction.
+ command elab Lean.Elab.Command.elabEval

syntax "#eval!"... [Lean.Parser.Command.evalBang]
  `#eval e` evaluates the expression `e` by compiling and evaluating it.
  ⏎
  * The command attempts to use `ToExpr`, `Repr`, or `ToString` instances to print the result.
  * If `e` is a monadic value of type `m ty`, then the command tries to adapt the monad `m`
    to one of the monads that `#eval` supports, which include `IO`, `CoreM`, `MetaM`, `TermElabM`, and `CommandElabM`.
    Users can define `MonadEval` instances to extend the list of supported monads.
  ⏎
  The `#eval` command gracefully degrades in capability depending on what is imported.
  Importing the `Lean.Elab.Command` module provides full capabilities.
  ⏎
  Due to unsoundness, `#eval` refuses to evaluate expressions that depend on `sorry`, even indirectly,
  since the presence of `sorry` can lead to runtime instability and crashes.
  This check can be overridden with the `#eval! e` command.
  ⏎
  Options:
  * If `eval.pp` is true (default: true) then tries to use `ToExpr` instances to make use of the
    usual pretty printer. Otherwise, only tries using `Repr` and `ToString` instances.
  * If `eval.type` is true (default: false) then pretty prints the type of the evaluated value.
  * If `eval.derive.repr` is true (default: true) then attempts to auto-derive a `Repr` instance
    when there is no other way to print the result.
  ⏎
  See also: `#reduce e` for evaluation by term reduction.
+ command elab Lean.Elab.Command.elabEvalBang

syntax "#exit"... [Lean.Parser.Command.exit]
+ command elab Lean.Elab.Command.elabExit
-/
#guard_msgs in
#help command+ "#e"

/-! #help conv -/

-- this is a long and constantly updated listing, we don't check the output
#guard_msgs(error, drop info) in
#help conv

/--
error: no conv declarations start with foobarbaz
-/
#guard_msgs in
#help conv foobarbaz

/--
info:
syntax "reduce"... [Lean.Parser.Tactic.Conv.reduce]
  Puts term in normal form, this tactic is meant for debugging purposes only.

syntax "repeat"... [Lean.Parser.Tactic.Conv.convRepeat_]
  `repeat convs` runs the sequence `convs` repeatedly until it fails to apply.

syntax "rewrite"... [Lean.Parser.Tactic.Conv.rewrite]
  `rw [thm]` rewrites the target using `thm`. See the `rw` tactic for more information.
-/
#guard_msgs in
#help conv "re"

/--
info:
syntax "reduce"... [Lean.Parser.Tactic.Conv.reduce]
  Puts term in normal form, this tactic is meant for debugging purposes only.
+ tactic elab Lean.Elab.Tactic.Conv.evalReduce

syntax "repeat"... [Lean.Parser.Tactic.Conv.convRepeat_]
  `repeat convs` runs the sequence `convs` repeatedly until it fails to apply.
+ macro Lean.Parser.Tactic.Conv._aux_Init_Conv___macroRules_Lean_Parser_Tactic_Conv_convRepeat__1

syntax "rewrite"... [Lean.Parser.Tactic.Conv.rewrite]
  `rw [thm]` rewrites the target using `thm`. See the `rw` tactic for more information.
+ tactic elab Lean.Elab.Tactic.Conv.evalRewrite
-/
#guard_msgs in
#help conv+ "re"

/-! `#help option` -/

-- this is a long and constantly updated listing, we don't check the output
#guard_msgs(error, drop info) in
#help option

/--
error: no options start with foobarbaz
-/
#guard_msgs in
#help option foobarbaz

/--
info:
option pp.instanceTypes : Bool := false
  (pretty printer) when printing explicit applications, show the types of inst-implicit arguments

option pp.instances : Bool := true
  (pretty printer) if set to false, replace inst-implicit arguments to explicit applications with
placeholders

option pp.instantiateMVars : Bool := true
  (pretty printer) instantiate mvars before delaborating
-/
#guard_msgs in
#help option pp.ins

/-! `#help tactic` -/

-- this is a long and constantly updated listing, we don't check the output
#guard_msgs(error, drop info) in
#help tactic

/--
error: no tactic declarations start with foobarbaz
-/
#guard_msgs in
#help tactic foobarbaz

/--
info:
syntax "by_cases"... [«tacticBy_cases_:_»]
  `by_cases (h :)? p` splits the main goal into two cases, assuming `h : p` in the first branch,
and `h : ¬ p` in the second branch.
-/
#guard_msgs in
#help tactic by

/--
info:
syntax "by_cases"... [«tacticBy_cases_:_»]
  `by_cases (h :)? p` splits the main goal into two cases, assuming `h : p` in the first branch, and `h : ¬ p` in the second branch.
+ macro «_aux_Init_ByCases___macroRules_tacticBy_cases_:__2»
+ macro «_aux_Init_ByCases___macroRules_tacticBy_cases_:__1»
-/
#guard_msgs in
#help tactic+ by

/-! #help term -/

-- this is a long and constantly updated listing, we don't check the output
#guard_msgs(error, drop info) in
#help term

/--
error: no term declarations start with foobarbaz
-/
#guard_msgs in
#help term foobarbaz

/--
info: syntax "debug_assert!"... [Lean.Parser.Term.debugAssert]
  `debug_assert! cond` panics if `cond` evaluates to `false` and the executing code has been built
  with debug assertions enabled (see the `debugAssertions` option).

syntax "decl_name%"... [Lean.Parser.Term.declName]
  A macro which evaluates to the name of the currently elaborating declaration.

syntax "default_or_ofNonempty%"... [Lean.Parser.Term.defaultOrOfNonempty]
-/
#guard_msgs in
#help term de

/--
info: syntax "debug_assert!"... [Lean.Parser.Term.debugAssert]
  `debug_assert! cond` panics if `cond` evaluates to `false` and the executing code has been built
  with debug assertions enabled (see the `debugAssertions` option).
+ term elab Lean.Elab.Term.elabDebugAssert

syntax "decl_name%"... [Lean.Parser.Term.declName]
  A macro which evaluates to the name of the currently elaborating declaration.
+ term elab Lean.Elab.Term.elabDeclName

syntax "default_or_ofNonempty%"... [Lean.Parser.Term.defaultOrOfNonempty]
+ term elab Lean.Elab.Term.Op.elabDefaultOrNonempty
-/
#guard_msgs in
#help term+ de

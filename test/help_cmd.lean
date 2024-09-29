import Batteries.Tactic.HelpCmd

/-! The #help command family

The #help command family currently contains these subcommands:

* #help attr
* #help cat
* #help cats
* #help command (abbrev for #help cat command)
* #help conv (abbrev for #help cat conv)
* #help option
* #help tactic (abbrev for #help cat tactic)
* #help term (abbrev for #help cat term)

All forms take an optional identifier prefix to narrow the search.

WARNING: Some of these tests will need occasional updates when new features are added and even when
some documentation is edited. This type of break will be unexpected but the fix will not be
unexpected! Just update the guard text to match the output after your addition.
-/

/-! #help attr -/

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

/-! #help cat -/

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

-- TODO: test #help cat+ somehow...

/-! #help cats -/

-- this is a long and constantly updated listing, we don't check the output
#guard_msgs(error, drop info) in
#help cats

/--
error: no syntax categories start with foobarbaz
-/
#guard_msgs in
#help cats foobarbaz

/--
info:
category prec [Lean.Parser.Category.prec]
  `prec` is a builtin syntax category for precedences. A precedence is a value
  that expresses how tightly a piece of syntax binds: for example `1 + 2 * 3` is
  parsed as `1 + (2 * 3)` because `*` has a higher pr0ecedence than `+`.
  Higher numbers denote higher precedence.
  In addition to literals like `37`, there are some special named priorities:
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

/-! #help command -/

-- this is a long and constantly updated listing, we don't check the output
#guard_msgs(error, drop info) in
#help command

/--
error: no command declarations start with foobarbaz
-/
#guard_msgs in
#help command foobarbaz

/--
info:
syntax "#eval"... [Lean.Parser.Command.eval]

syntax "#eval!"... [Lean.Parser.Command.evalBang]

syntax "#exit"... [Lean.Parser.Command.exit]
-/
#guard_msgs in
#help command "#e"

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

/-! #help option -/

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

/-! #help tactic -/

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

/-! #help tactic -/

-- this is a long and constantly updated listing, we don't check the output
#guard_msgs(error, drop info) in
#help term

/--
error: no term declarations start with foobarbaz
-/
#guard_msgs in
#help term foobarbaz

/--
info:
syntax "decl_name%"... [Lean.Parser.Term.declName]
  A macro which evaluates to the name of the currently elaborating declaration.

syntax "default_or_ofNonempty%"... [Lean.Parser.Term.defaultOrOfNonempty]
-/
#guard_msgs in
#help term de

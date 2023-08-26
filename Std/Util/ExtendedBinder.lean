/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner
-/
import Lean.Elab.MacroArgUtil
import Lean.Linter.MissingDocs

/-!
Defines an extended binder syntax supporting `∀ ε > 0, ...` etc.
-/

namespace Std.ExtendedBinder
open Lean

/--
The syntax category of binder predicates contains predicates like `> 0`, `∈ s`, etc.
(`: t` should not be a binder predicate because it would clash with the built-in syntax for ∀/∃.)
-/
declare_syntax_cat binderPred

/--
`satisfies_binder_pred% t pred` expands to a proposition expressing that `t` satisfies `pred`.
-/
syntax "satisfies_binder_pred% " term:max binderPred : term

-- Extend ∀ and ∃ to binder predicates.

/--
The notation `∃ x < 2, p x` is shorthand for `∃ x, x < 2 ∧ p x`,
and similarly for other binary relations defined as being binder predicates.
-/
syntax "∃ " term:max binderPred ", " term : term
/--
The notation `∀ x < 2, p x` is shorthand for `∀ x, x < 2 → p x`,
and similarly for other binary relations defined as being binder predicates.
-/
syntax "∀ " term:max binderPred ", " term : term

macro_rules
  | `(∃ $x:term $pred:binderPred, $p) =>
    match x with
    | `($x:ident) => `(∃ $x:ident, satisfies_binder_pred% $x $pred ∧ $p)
    | `(_)        => `(∃ x, satisfies_binder_pred% x $pred ∧ $p)
    | _           => `(∃ x, satisfies_binder_pred% x $pred ∧ match x with | $x => $p)

macro_rules
  | `(∀ $x:term $pred:binderPred, $p) =>
    match x with
    | `($x:ident) => `(∀ $x:ident, satisfies_binder_pred% $x $pred → $p)
    | `(_)        => `(∀ x, satisfies_binder_pred% x $pred → $p)
    | _           => `(∀ x, satisfies_binder_pred% x $pred → match x with | $x => $p)

-- We also provide special versions of ∀/∃ that take a list of extended binders.
-- The built-in binders are not reused because that results in overloaded syntax.

/--
An extended binder has the form `x`, `x : ty`, or `x pred`
where `pred` is a `binderPred` like `< 2`.
The pattern `x` can be any term.
-/
syntax extBinder := term:max ((" : " term) <|> binderPred)?
/-- A extended binder in parentheses -/
syntax extBinderParenthesized := " (" extBinder ")" -- TODO: inlining this definition breaks
/-- A list of parenthesized binders -/
syntax extBinderCollection := extBinderParenthesized+
/-- A list of parenthesized binders or a single (unparenthesized) binder. -/
syntax extBinders := extBinderCollection <|> (ppSpace extBinder)

/-- The syntax `∃ᵉ (x < 2) (y < 3), p x y` is shorthand for `∃ x < 2, ∃ y < 3, p x y`. -/
syntax "∃ᵉ" extBinders ", " term : term
/-- Convert `extBinderCollection` into nested `extBinder`s. -/
macro_rules
  | `(∃ᵉ $[($ps:extBinder)]*, $b) => ps.foldrM (fun p e => `(∃ᵉ $p:extBinder, $(⟨e⟩))) b
/-- Handle individual `extBinder`s. -/
macro_rules
  | `(∃ᵉ $x:term, $b) => `(Exists fun $x => $b)
  | `(∃ᵉ $x:term : $ty:term, $b) => `(@Exists $ty fun $x => $b)
  | `(∃ᵉ $x:term $p:binderPred, $b) => `(∃ $x:term $p:binderPred, $b)

/-- The syntax `∀ᵉ (x < 2) (y < 3), p x y` is shorthand for `∀ x < 2, ∀ y < 3, p x y`. -/
syntax "∀ᵉ" extBinders ", " term : term
/-- Convert `extBinderCollection` into nested `extBinder`s. -/
macro_rules
  | `(∀ᵉ $[($ps:extBinder)]*, $b) => ps.foldrM (fun p e => `(∀ᵉ $p:extBinder, $(⟨e⟩))) b
/-- Handle individual `extBinder`s. -/
macro_rules
  | `(∀ᵉ _, $b) => `(∀ _, $b)
  | `(∀ᵉ $x:ident, $b) => `(∀ $x:ident, $b)
  | `(∀ᵉ $x:term : $ty:term, $b) =>
    match x with
    | `($x:ident) => `(∀ $x:ident : $ty:term, $b)
    | `(_)        => `(∀ _ : $ty:term, $b)
    | _           => `(∀ x : $ty:term, match x with | $x => $b)
  | `(∀ᵉ $x:term $p:binderPred, $b) => `(∀ $x:term $p:binderPred, $b)

open Parser.Command in
/--
Declares a binder predicate.  For example:
```
binder_predicate x " > " y:term => `($x > $y)
```
-/
syntax (name := binderPredicate) (docComment)? (Parser.Term.attributes)? (attrKind)?
  "binder_predicate" optNamedName optNamedPrio ppSpace ident (ppSpace macroArg)* " => "
    term : command

-- adapted from the macro macro
open Elab Command in
elab_rules : command
  | `($[$doc?:docComment]? $[@[$attrs?,*]]? $attrKind:attrKind binder_predicate%$tk
      $[(name := $name?)]? $[(priority := $prio?)]? $x $args:macroArg* => $rhs) => do
    let prio ← liftMacroM do evalOptPrio prio?
    let (stxParts, patArgs) := (← args.mapM expandMacroArg).unzip
    let name ← match name? with
      | some name => pure name.getId
      | none => liftMacroM do mkNameFromParserSyntax `binderTerm (mkNullNode stxParts)
    let nameTk := name?.getD (mkIdentFrom tk name)
    /- The command `syntax [<kind>] ...` adds the current namespace to the syntax node kind.
    So, we must include current namespace when we create a pattern for the following
    `macro_rules` commands. -/
    let pat : TSyntax `binderPred := ⟨(mkNode ((← getCurrNamespace) ++ name) patArgs).1⟩
    elabCommand <|<-
    `($[$doc?:docComment]? $[@[$attrs?,*]]? $attrKind:attrKind syntax%$tk
        (name := $nameTk) (priority := $(quote prio)) $[$stxParts]* : binderPred
      $[$doc?:docComment]? macro_rules%$tk
        | `(satisfies_binder_pred% $$($x):term $pat:binderPred) => $rhs)

open Linter.MissingDocs Parser Term in
/-- Missing docs handler for `binder_predicate` -/
@[missing_docs_handler binderPredicate]
def checkBinderPredicate : SimpleHandler := fun stx => do
  if stx[0].isNone && stx[2][0][0].getKind != ``«local» then
    if stx[4].isNone then lint stx[3] "binder predicate"
    else lintNamed stx[4][0][3] "binder predicate"

/-- Declare `∃ x > y, ...` as syntax for `∃ x, x > y ∧ ...` -/
binder_predicate x " > " y:term => `($x > $y)
/-- Declare `∃ x ≥ y, ...` as syntax for `∃ x, x ≥ y ∧ ...` -/
binder_predicate x " ≥ " y:term => `($x ≥ $y)
/-- Declare `∃ x < y, ...` as syntax for `∃ x, x < y ∧ ...` -/
binder_predicate x " < " y:term => `($x < $y)
/-- Declare `∃ x ≤ y, ...` as syntax for `∃ x, x ≤ y ∧ ...` -/
binder_predicate x " ≤ " y:term => `($x ≤ $y)

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

/--
A syntax category for macros that do calculations regarding binders.
For example, this supports querying for the inverse to `satisfies_binder_pred%`.
-/
declare_syntax_cat binderCalc

/-- This syntax represents values that could be passed to `satisfies_binder_pred%`. -/
syntax "the_binder_pred " term:max binderPred : binderCalc

/-- Represents a query that expands to `the_binder_pred` if there is an answer. -/
syntax "get_binder_pred_of_prop " term : binderCalc

/-- Evaluates a `binderCalc` calculation by macro expanding until completion. -/
partial def runBinderCalc (q : TSyntax `binderCalc) : MacroM (TSyntax `binderCalc) := do
  match ← expandMacro? q with
  | none => return q
  | some q' => runBinderCalc ⟨q'⟩

/-- Given a proposition (such as `x < 5`), returns `(x, < 5)` if
`get_binder_pred_of_prop` knows about it. This inverts `satisfies_binder_pred%`. -/
def getBinderPredOfProp (p : Term) : MacroM (Option (Term × TSyntax `binderPred)) := do
  let q ← `(binderCalc| get_binder_pred_of_prop $p)
  match ← runBinderCalc q with
  | `(binderCalc| the_binder_pred $x $pred) => return (x, pred)
  | _ => return none

/-! ### Extend ∀ and ∃ to binder predicates. -/

/--
The notation `∃ x < 2, p x` is shorthand for `∃ x, x < 2 ∧ p x`,
and similarly for other binary operators.
-/
syntax "∃ " binderIdent binderPred ", " term : term
/--
The notation `∀ x < 2, p x` is shorthand for `∀ x, x < 2 → p x`,
and similarly for other binary operators.
-/
syntax "∀ " binderIdent binderPred ", " term : term

macro_rules
  | `(∃ $x:ident $pred:binderPred, $p) =>
    `(∃ $x:ident, satisfies_binder_pred% $x $pred ∧ $p)
  | `(∃ _ $pred:binderPred, $p) =>
    `(∃ x, satisfies_binder_pred% x $pred ∧ $p)

macro_rules
  | `(∀ $x:ident $pred:binderPred, $p) =>
    `(∀ $x:ident, satisfies_binder_pred% $x $pred → $p)
  | `(∀ _ $pred:binderPred, $p) =>
    `(∀ x, satisfies_binder_pred% x $pred → $p)

-- We also provide special versions of ∀/∃ that take a list of extended binders.
-- The built-in binders are not reused because that results in overloaded syntax.

/--
An extended binder has the form `x`, `x : ty`, or `x pred`
where `pred` is a `binderPred` like `< 2`.
-/
syntax extBinder := binderIdent ((" : " term) <|> binderPred)?
/-- A extended binder in parentheses -/
syntax extBinderParenthesized := " (" extBinder ")" -- TODO: inlining this definition breaks
/-- A list of parenthesized binders -/
syntax extBinderCollection := extBinderParenthesized*
/-- A single (unparenthesized) binder, or a list of parenthesized binders -/
syntax extBinders := (ppSpace extBinder) <|> extBinderCollection

/-- The syntax `∃ᵉ (x < 2) (y < 3), p x y` is shorthand for `∃ x < 2, ∃ y < 3, p x y`. -/
syntax "∃ᵉ" extBinders ", " term : term
macro_rules
  | `(∃ᵉ, $b) => pure b
  | `(∃ᵉ ($p:extBinder) $[($ps:extBinder)]*, $b) =>
    `(∃ᵉ $p:extBinder, ∃ᵉ $[($ps:extBinder)]*, $b)
macro_rules -- TODO: merging the two macro_rules breaks expansion
  | `(∃ᵉ $x:binderIdent, $b) => `(∃ $x:binderIdent, $b)
  | `(∃ᵉ $x:binderIdent : $ty:term, $b) => `(∃ $x:binderIdent : $ty:term, $b)
  | `(∃ᵉ $x:binderIdent $p:binderPred, $b) => `(∃ $x:binderIdent $p:binderPred, $b)

/-- The syntax `∀ᵉ (x < 2) (y < 3), p x y` is shorthand for `∀ x < 2, ∀ y < 3, p x y`. -/
syntax "∀ᵉ" extBinders ", " term : term
macro_rules
  | `(∀ᵉ, $b) => pure b
  | `(∀ᵉ ($p:extBinder) $[($ps:extBinder)]*, $b) =>
    `(∀ᵉ $p:extBinder, ∀ᵉ $[($ps:extBinder)]*, $b)
macro_rules -- TODO: merging the two macro_rules breaks expansion
  | `(∀ᵉ _, $b) => `(∀ _, $b)
  | `(∀ᵉ $x:ident, $b) => `(∀ $x:ident, $b)
  | `(∀ᵉ _ : $ty:term, $b) => `(∀ _ : $ty:term, $b)
  | `(∀ᵉ $x:ident : $ty:term, $b) => `(∀ $x:ident : $ty:term, $b)
  | `(∀ᵉ $x:binderIdent $p:binderPred, $b) => `(∀ $x:binderIdent $p:binderPred, $b)

/-! ### `binder_predicate` command -/

open Parser.Command in
/--
Declares a binder predicate.  For example:
```
binder_predicate x " > " y:term => x > y
```
-/
syntax (name := binderPredicate) (docComment)? (Parser.Term.attributes)? (attrKind)?
  "binder_predicate" optNamedName optNamedPrio ppSpace ident (ppSpace macroArg)* " => "
    term : command

open Syntax in
/-- Wrap all occurrences of the given `ident` nodes in antiquotations.
(from a private function in Lean.Elab.Notation) -/
private partial def antiquote (vars : Array Syntax) (stx : Syntax) : Syntax :=
  match stx with
  | `($id:ident) =>
    if (vars.findIdx? (fun var => var.getId == id.getId)).isSome then
      mkAntiquotNode id (kind := `term) (isPseudoKind := true)
    else
      stx
  | _ => match stx with
    | Syntax.node i k args => Syntax.node i k (args.map (antiquote vars))
    | stx => stx

-- adapted from the macro macro and the notation macro
open Elab Command in
elab_rules : command
  | `($[$doc?:docComment]? $[@[$attrs?,*]]? $attrKind:attrKind binder_predicate%$tk
      $[(name := $name?)]? $[(priority := $prio?)]? $x $args:macroArg* => $rhs) => do
    let prio ← liftMacroM do evalOptPrio prio?
    let (stxParts, patArgs) := (← args.mapM expandMacroArg).unzip
    let vars := args.filterMap fun
        | `(Parser.Command.macroArg| $id:ident:$(_)) => some id
        | `(Parser.Command.macroArg| $(_):stx)       => none
        | _                           => none
    let qrhs : Term := ⟨antiquote (vars.push x) rhs⟩
    let name ← match name? with
      | some name => pure name.getId
      | none => liftMacroM do mkNameFromParserSyntax `binderTerm (mkNullNode stxParts)
    let nameTk := name?.getD (mkIdentFrom tk name)
    /- The command `syntax [<kind>] ...` adds the current namespace to the syntax node kind.
    So, we must include current namespace when we create a pattern for the following
    `macro_rules` commands. -/
    let pat : TSyntax `binderPred := ⟨(mkNode ((← getCurrNamespace) ++ name) patArgs).1⟩
    elabCommand <| ←
      `($[$doc?:docComment]? $[@[$attrs?,*]]? $attrKind:attrKind syntax%$tk
          (name := $nameTk) (priority := $(quote prio)) $[$stxParts]* : binderPred
        $[$doc?:docComment]? macro_rules%$tk
          | `(satisfies_binder_pred% $$($x):term $pat:binderPred) => `($qrhs)
        macro_rules%$tk
          | `(binderCalc| get_binder_pred_of_prop $qrhs) =>
            let x := Syntax.missing -- Workaround for expandMacroArg on strings
            `(binderCalc| the_binder_pred $$($x):term $pat:binderPred))

open Linter.MissingDocs Parser Term in
/-- Missing docs handler for `binder_predicate` -/
@[missing_docs_handler binderPredicate]
def checkBinderPredicate : SimpleHandler := fun stx => do
  if stx[0].isNone && stx[2][0][0].getKind != ``«local» then
    if stx[4].isNone then lint stx[3] "binder predicate"
    else lintNamed stx[4][0][3] "binder predicate"

/-- Declare `∃ x > y, ...` as syntax for `∃ x, x > y ∧ ...` -/
binder_predicate x " > " y:term => x > y
/-- Declare `∃ x ≥ y, ...` as syntax for `∃ x, x ≥ y ∧ ...` -/
binder_predicate x " ≥ " y:term => x ≥ y
/-- Declare `∃ x < y, ...` as syntax for `∃ x, x < y ∧ ...` -/
binder_predicate x " < " y:term => x < y
/-- Declare `∃ x ≤ y, ...` as syntax for `∃ x, x ≤ y ∧ ...` -/
binder_predicate x " ≤ " y:term => x ≤ y

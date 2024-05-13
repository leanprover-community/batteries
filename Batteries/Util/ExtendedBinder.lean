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

namespace Batteries.ExtendedBinder
open Lean


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

open Linter.MissingDocs Parser Term in
/-- Missing docs handler for `binder_predicate` -/
@[missing_docs_handler binderPredicate]
def checkBinderPredicate : SimpleHandler := fun stx => do
  if stx[0].isNone && stx[2][0][0].getKind != ``«local» then
    if stx[4].isNone then lint stx[3] "binder predicate"
    else lintNamed stx[4][0][3] "binder predicate"

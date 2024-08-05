/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner
-/

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

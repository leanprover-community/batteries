/-
Copyright (c) 2021 Gabriel Ebner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner
-/
import Lean

/-!
# Stub for try-this support

Lean 4 does not yet support code actions
to present tactic suggestions in the editor.
This file contains a preliminary API
that tactics can call to show suggestions.
-/
namespace Tactic.TryThis

open Lean Elab Elab.Tactic PrettyPrinter Meta

/-- Replace subexpressions like `?m.1234` with `?_` so it can be copy-pasted. -/
partial def replaceMVarsByUnderscores [Monad m] [MonadQuotation m]
    (s : Syntax) : m Syntax :=
  s.replaceM fun s => if let `(?$_:ident) := s then `(?_) else pure none

/-- Delaborate `e` into an expression suitable for use in `refine`. -/
def delabToRefinableSyntax (e : Expr) : TermElabM Term :=
  return ⟨← replaceMVarsByUnderscores (← delab e)⟩

/-- Add a "try this" suggestion. (TODO: this depends on code action support) -/
def addSuggestion [Monad m] [MonadLog m] [AddMessageContext m] [MonadOptions m]
    (origStx : Syntax) (suggestion : Syntax) : m Unit :=
  logInfoAt origStx m!"{suggestion}"

/-- Add a `exact e` or `refine e` suggestion. (TODO: this depends on code action support) -/
def addExactSuggestion (origTac : Syntax) (e : Expr) : TacticM Unit := do
  let stx ← delabToRefinableSyntax e
  let tac ← if e.hasExprMVar then `(tactic| refine $stx) else `(tactic| exact $stx)
  addSuggestion origTac tac

/-- Add a term suggestion. (TODO: this depends on code action support) -/
def addTermSuggestion (origTerm : Syntax) (e : Expr) : TermElabM Unit := do
  addSuggestion origTerm (← delabToRefinableSyntax e)

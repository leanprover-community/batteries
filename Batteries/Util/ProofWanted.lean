/-
Copyright (c) 2023 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Thrane Christiansen, Kim Morrison
-/
module

public import Batteries.Tactic.Lint.Misc
public meta import Lean.Elab.Command
public meta import Lean.Elab.Term
public meta import Batteries.Lean.Syntax

@[expose] public section

/-!
# The `proof_wanted` command

`proof_wanted name binders : T` records `T` as a wanted theorem. It elaborates to a private
placeholder `def name binders : ProofWanted T := ⟨⟩` — a sound, file-local trace. Inside another
`proof_wanted` statement, the bracket syntax `❰foo❱` lets you assume an earlier `proof_wanted`.
The brackets desugar to fresh hypothesis binders, so the wanted statement honestly records the
dependency: "if `foo` holds, then …" — no axioms or sorries are introduced.
-/

/-- Wrapper recording that a `proof_wanted` of statement `α` has been declared. -/
structure ProofWanted (α : Sort u) : Type where
  /-- The trivial constructor; carries no information. -/
  mk ::

/-- Reducible accessor so a binder of type `ProofWanted.Stmt foo` reduces to `foo`'s
statement. Used by the desugaring of `❰foo❱`. -/
@[reducible, nolint unusedArguments]
def ProofWanted.Stmt {α : Sort u} (_ : ProofWanted α) : Sort u := α

end

public meta section

open Lean Elab Command

/-- Internal bracket syntax `❰foo❱` for referencing an earlier `proof_wanted`.
Only meaningful inside the statement of a `proof_wanted`; the term elaborator
errors everywhere else. -/
syntax (name := proofWantedRef) "❰" ident "❱" : term

/-- Elaborator that errors when `❰…❱` is used outside a `proof_wanted` statement. -/
@[term_elab proofWantedRef]
def elabProofWantedRef : Term.TermElab := fun _ _ =>
  throwError "`❰…❱` may only appear inside the statement of `proof_wanted`"

/-- This proof would be a welcome contribution to the library!

The syntax of `proof_wanted` declarations is just like that of `theorem`, but without `:=` or the
proof. Lean checks that `proof_wanted` declarations are well-formed (e.g. it ensures that all the
mentioned names are in scope, and that the theorem statement is a valid proposition), and records a
private placeholder declaration of type `... → ProofWanted statement`.

Modifiers (such as `@[simp]`) are accepted for syntactic compatibility with `theorem` but are
currently ignored.

Inside another `proof_wanted`'s statement, write `❰foo❱` to assume an earlier `proof_wanted` named
`foo`. The bracket must appear inside the *statement* (it has no meaning in a proof body — there
is none). It desugars to a fresh hypothesis binder of the matching type, so the resulting wanted
statement is literally "if `foo` holds, then …". This keeps the trace sound — no axioms or
sorries are introduced — while letting one `proof_wanted` build on another. Brackets only
resolve names within the current file, since the placeholders are `private`.

Typical usage:
```
proof_wanted seventeen_eq_thirtyseven : 17 = 37

proof_wanted seventeen_in_fifty :
    (⟨17, by rw [❰seventeen_eq_thirtyseven❱]; decide⟩ : Fin 50) = 0
```
-/
@[command_parser]
def «proof_wanted» := leading_parser
  Parser.Command.declModifiers false >> "proof_wanted" >>
    Parser.Command.declId >> Parser.ppIndent Parser.Command.declSig

/-- Walk a syntax tree, throwing on the first `proofWantedRef` node found. -/
private def rejectRefsIn (loc : String) (stx : Syntax) : CommandElabM Unit := do
  let _ ← stx.replaceM fun s => do
    if s.getKind == ``proofWantedRef then
      throwErrorAt s "`❰…❱` may not appear inside {loc} of `proof_wanted`"
    return none

/-- Build a fresh hypothesis identifier name based on the last component of `n`. -/
private def freshHypName (n : Name) : CommandElabM Name := do
  let baseStr := match n.componentsRev.head? with
    | some (.str _ s) => "h_" ++ s
    | _ => "h_ref"
  liftCoreM <| Lean.mkFreshUserName (Name.mkSimple baseStr)

/-- Check that `nm` is a previously-declared `proof_wanted` (i.e. its type unifies with
`ProofWanted ?α` and `?α` is a proposition). Throws a descriptive error otherwise. -/
private def validateProofWantedRef (nm : Name) (stx : Syntax) : CommandElabM Unit := do
  Command.liftTermElabM do
    let info ← getConstInfo nm
    let u ← Lean.Meta.mkFreshLevelMVar
    let α ← Lean.Meta.mkFreshExprMVar (some (Lean.mkSort u))
    let expected := Lean.mkApp (Lean.mkConst ``ProofWanted [u]) α
    unless ← Lean.Meta.isDefEq info.type expected do
      throwErrorAt stx
        "`{stx}` is not a `proof_wanted` declaration (its type is not `ProofWanted _`)"
    unless ← Lean.Meta.isProp (← instantiateMVars α) do
      throwErrorAt stx
        "`{stx}` is a `ProofWanted`, but its statement is not a proposition"

/-- Elaborate a `proof_wanted` declaration into a private placeholder `def` of type `ProofWanted`,
expanding any `❰…❱` references to fresh hypothesis binders. -/
@[command_elab «proof_wanted»]
def elabProofWanted : CommandElab
  | `($_mods:declModifiers proof_wanted $name $args* : $res) => do
    -- (1) Brackets aren't allowed inside binder types in this version.
    for arg in args do
      rejectRefsIn "binder types" arg.raw
    -- (2) Walk the result type, replacing each `❰x❱` reference with a fresh hypothesis ident.
    -- Each occurrence (even repeated `❰x❱`s for the same `x`) gets its own binder.
    let hypOrderRef : IO.Ref (Array (Name × TSyntax `ident)) ← IO.mkRef #[]
    let res' ← res.raw.replaceM fun s => do
      unless s.getKind == ``proofWantedRef do return none
      let identStx : Syntax.Ident := ⟨s[1]⟩
      let nm ← liftCoreM <| Elab.realizeGlobalConstNoOverloadWithInfo identStx
      validateProofWantedRef nm identStx
      let fresh ← freshHypName nm
      let hyp : TSyntax `ident := mkIdent fresh
      hypOrderRef.modify (·.push (nm, hyp))
      return some hyp.raw
    let res' : TSyntax `term := ⟨res'⟩
    let order : Array (Name × TSyntax `ident) ← hypOrderRef.get
    -- (3) Build the extra bracketed binders.
    let extraBinders ← order.mapM fun (nm, hyp) =>
      `(Parser.Term.bracketedBinderF| ($hyp : ProofWanted.Stmt $(mkIdent nm)))
    -- (4) Emit the placeholder. Binders go on the `def` rather than inside `ProofWanted (∀ …)`,
    -- which keeps the syntax-level splice simple at the cost that `❰name❱` only validates when
    -- `name` itself has no binders (its type must unify with `ProofWanted _`). The `(_ : Prop)`
    -- ascription preserves the "type is not a proposition" check the old `theorem` form gave
    -- for free, and `linter.unusedVariables` is silenced so user binders that only appear in
    -- the statement don't trigger warnings.
    elabCommand <| ← `(
      section
      set_option linter.unusedVariables false
      private def $name $args* $extraBinders* : ProofWanted (($res' : Prop)) := ⟨⟩
      end)
  | _ => throwUnsupportedSyntax

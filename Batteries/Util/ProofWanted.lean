/-
Copyright (c) 2023 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Thrane Christiansen, Kim Morrison
-/
module

public import Batteries.Tactic.Lint.Misc
public meta import Lean.Elab.Command
public meta import Lean.Elab.Term
public meta import Lean.Meta.Tactic.TryThis
public meta import Batteries.Lean.Syntax

/-!
# The `proof_wanted` command

Use `proof_wanted name binders : T` to mark a theorem the library should eventually contain
without blocking compilation. The declaration elaborates to a private placeholder `def name
binders : ProofWanted T := ⟨⟩`, so the wanted result is visible to downstream files and tools
by type rather than by side-channel.

Inside another `proof_wanted`, `❰foo❱` references an earlier `proof_wanted`; for parametrised
`foo`, write `❰foo❱ x y` to apply it. The brackets desugar to fresh hypothesis binders, so the
dependency appears in the recorded type.

A partial proof may be supplied with `proof_wanted name binders : T := body`. The body must
reference at least one `❰…❱` (in the statement or the body); a complete proof should be a
`theorem` instead, and the error includes a `Try this:` suggestion to that effect.

The `❰` and `❱` characters (U+2770, U+2771) are entered as `\h<` and `\h>` with the standard
Lean input method.
-/

/-- Wrapper recording that a `proof_wanted` of statement `α` has been declared. -/
public structure ProofWanted (α : Sort u) : Type where
  /-- The trivial constructor; carries no information. -/
  mk ::

/-- Reducible accessor so a binder of type `ProofWanted.Stmt foo` reduces to `foo`'s
statement. Used by the desugaring of `❰foo❱`. -/
@[reducible, nolint unusedArguments, expose]
public def ProofWanted.Stmt {α : Sort u} (_ : ProofWanted α) : Sort u := α

public meta section

open Lean Elab Command

/-- Internal bracket syntax `❰foo❱` for referencing an earlier `proof_wanted`.
Only meaningful inside the statement or body of a `proof_wanted`; the term elaborator
errors everywhere else. -/
syntax (name := proofWantedRef) "❰" ident "❱" : term

/-- Elaborator that errors when `❰…❱` is used outside a `proof_wanted`. -/
@[term_elab proofWantedRef]
def elabProofWantedRef : Term.TermElab := fun _ _ =>
  throwError "`❰…❱` may only appear inside the statement or body of `proof_wanted`"

/-- This proof would be a welcome contribution to the library!

The syntax of `proof_wanted` declarations is just like that of `theorem`. Without `:=` and a
proof body it records a wanted theorem; with one it records a partial proof that still depends on
other wanted lemmas. Lean checks that `proof_wanted` declarations are well-formed (e.g. it ensures
that all the mentioned names are in scope, and that the theorem statement is a valid proposition),
and records a private placeholder declaration of type `... → ProofWanted statement`.

Modifiers (such as `@[simp]`) are accepted for syntactic compatibility with `theorem` but are
currently ignored.

Inside another `proof_wanted`, write `❰foo❱` to reference an earlier `proof_wanted` named `foo`.
The bracket may appear in the statement or the body, and each distinct reference becomes a fresh
hypothesis binder of the matching type. For parametrised `foo : ∀ args, ProofWanted _`, the
binder type is itself Π-quantified, so `❰foo❱ x y` applies the parameter to `x y`. `❰foo❱` only
resolves names within the current file, since the placeholders are `private`.

A body must reference at least one `❰…❱` (in the statement or the body); otherwise the body is
a complete proof and the declaration should be a `theorem`.

Typical usage:
```
-- A parameterless wanted fact:
proof_wanted size_of_two_pushes_onto_empty :
    ((#[] : Array Nat).push 1 |>.push 2).size = 2

-- Referencing an earlier `proof_wanted` inside a statement (here in the `Fin`
-- bound proof, which rewrites by the wanted fact):
proof_wanted first_index_after_two_pushes :
    (⟨0, by rw [❰size_of_two_pushes_onto_empty❱]; decide⟩
      : Fin ((#[] : Array Nat).push 1 |>.push 2).size).val = 0

-- A parametrised wanted fact:
proof_wanted size_after_two_pushes {α : Type _} (a : Array α) (x y : α) :
    ((a.push x).push y).size = a.size + 2

-- A partial proof may be supplied with `:= body`, deferring the harder step via `❰…❱`:
proof_wanted size_after_three_pushes {α : Type _} (a : Array α) (x y z : α) :
    (((a.push x).push y).push z).size = a.size + 3 := by
  rw [Array.size_push, ❰size_after_two_pushes❱ a x y]
```
-/
@[command_parser]
def «proof_wanted» := leading_parser
  Parser.Command.declModifiers false >> "proof_wanted" >>
    Parser.Command.declId >> Parser.ppIndent Parser.Command.declSig >>
    Parser.optional (" := " >> Parser.termParser)

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

/-- Information returned by `validateProofWantedRef`: the parameter-binder type syntax, and a
flag saying whether the recorded statement is a typeclass — informs whether the caller emits
`[c_foo : …]` (instance) or the default `{c_foo : …}` (implicit). -/
private structure ProofWantedRefInfo where
  binderType : TSyntax `term
  /-- `true` if the wanted's payload is a typeclass. The generated parameter is then an instance
  binder so Lean's instance synth can find it. -/
  isClass : Bool

/-- Check that `nm` is a previously-declared `proof_wanted` (i.e. its type, after stripping any
Π binders, unifies with `ProofWanted ?α` and `?α` is a proposition), and return the parameter-
binder type to use when referencing it plus a class-payload flag. For parameterless `nm`, the
binder type is `ProofWanted.Stmt foo`; for parametrised `nm : ∀ args, ProofWanted (P args)`, it
is `∀ args, ProofWanted.Stmt (foo args)`, so a user can write `❰foo❱ x y` and have the bracket
desugar to the parameter applied to `x y`.

We construct the binder type directly as syntax (rather than via `Meta` + delab) to avoid two
round-trip pitfalls: pretty-printer dot notation can elide implicit arguments (so for `foo {n :
Nat} : …`, `(foo n).Stmt` would print as `foo.Stmt` and lose `n`), and a delab over fresh
universe metavariables emits `sorry` placeholders. -/
private def validateProofWantedRef (nm : Name) (stx : Syntax) :
    CommandElabM ProofWantedRefInfo := do
  Command.liftTermElabM <| open Lean.Meta in do
    let info ← getConstInfo nm
    forallTelescope info.type fun fvars body => do
      let u ← mkFreshLevelMVar
      let α ← mkFreshExprMVar (some (Lean.mkSort u))
      unless ← isDefEq body (Lean.mkApp (Lean.mkConst ``ProofWanted [u]) α) do
        throwErrorAt stx
          "`{stx}` is not a `proof_wanted` declaration \
           (its type doesn't end in `ProofWanted _`)"
      let αInst ← Lean.instantiateMVars α
      unless ← isProp αInst do
        throwErrorAt stx
          "`{stx}` is a `ProofWanted`, but its statement is not a proposition"
      let env ← getEnv
      let isCls : Bool := match αInst.getAppFn with
        | .const n _ => Lean.isClass env n
        | _ => false
      -- Build syntax `∀ <foo's binders>, ProofWanted.Stmt (@foo.{us} arg1 ... argN)`. The `@`
      -- keeps every implicit argument explicit so the syntax round-trips; the universe
      -- annotations bind to `nm`'s own level params (auto-bound for the enclosing `proof_wanted`).
      let fooIdent := mkIdent nm
      let levelStxs : Array (TSyntax `level) ←
        info.levelParams.toArray.mapM fun u => `(level| $(mkIdent u):ident)
      let argIdents : Array (TSyntax `term) ← fvars.mapM fun fvar => do
        let decl ← fvar.fvarId!.getDecl
        return ⟨mkIdent decl.userName⟩
      let appliedSyn : TSyntax `term ←
        if levelStxs.isEmpty then
          `(@$fooIdent $argIdents*)
        else
          `(@$fooIdent:ident.{$levelStxs,*} $argIdents*)
      let accessorIdent := mkIdent ``ProofWanted.Stmt
      let bodySyn ← `($accessorIdent $appliedSyn)
      -- Wrap with Π binders, preserving each binder's name, type, and binder info.
      let mut binderTySyn := bodySyn
      for fvar in fvars.reverse do
        let decl ← fvar.fvarId!.getDecl
        let nameId := mkIdent decl.userName
        -- Delab only the *type* of each binder; this is a plain type expression and doesn't
        -- hit the dot-notation problem that motivated the manual construction above.
        let typeSyn ← PrettyPrinter.delab decl.type
        binderTySyn ← match decl.binderInfo with
          | .default        => `(($nameId : $typeSyn) → $binderTySyn)
          | .implicit       => `({$nameId : $typeSyn} → $binderTySyn)
          | .strictImplicit => `(⦃$nameId : $typeSyn⦄ → $binderTySyn)
          | .instImplicit   => `([$nameId : $typeSyn] → $binderTySyn)
      return { binderType := binderTySyn, isClass := isCls }

/-- Elaborate a `proof_wanted` declaration into a private placeholder `def` of type `ProofWanted`,
expanding any `❰…❱` references to fresh hypothesis binders. If a body is supplied, it is
type-checked against the statement; the placeholder still carries no proof. -/
@[command_elab «proof_wanted»]
def elabProofWanted : CommandElab := fun stx => do
  match stx with
  | `($mods:declModifiers proof_wanted $name $args* : $res $[:= $body?]?) => do
    for arg in args do
      rejectRefsIn "binder types" arg.raw
    -- Brackets are deduplicated by referenced name across both the statement and the body, so
    -- repeated `❰x❱` references share one hypothesis binder.
    let nameToHypRef : IO.Ref (NameMap (TSyntax `ident)) ← IO.mkRef {}
    let hypOrderRef : IO.Ref (Array (TSyntax `ident × ProofWantedRefInfo)) ← IO.mkRef #[]
    let rewriteRefs (s : Syntax) : CommandElabM Syntax := s.replaceM fun node => do
      unless node.getKind == ``proofWantedRef do return none
      let identStx : Syntax.Ident := ⟨node[1]⟩
      let nm ← liftCoreM <| Elab.realizeGlobalConstNoOverloadWithInfo identStx
      let m ← nameToHypRef.get
      match m.find? nm with
      | some h => return some h.raw
      | none =>
        let refInfo ← validateProofWantedRef nm identStx
        let fresh ← freshHypName nm
        let hyp : TSyntax `ident := mkIdent fresh
        nameToHypRef.set (m.insert nm hyp)
        hypOrderRef.modify (·.push (hyp, refInfo))
        return some hyp.raw
    let res' : TSyntax `term := ⟨← rewriteRefs res.raw⟩
    let body'? : Option (TSyntax `term) ← body?.mapM fun b => return ⟨← rewriteRefs b.raw⟩
    let order ← hypOrderRef.get
    -- A body with no brackets anywhere is a complete proof; suggest `theorem` instead.
    if let some body := body? then
      if order.isEmpty then
        let thmStx ← `(command|
          $mods:declModifiers theorem $name $args* : $res := $body)
        liftCoreM <| Lean.Meta.Tactic.TryThis.addSuggestion stx
          { suggestion := .tsyntax thmStx }
        throwError
          "`proof_wanted` with a body but no `❰…❱` reference is just a `theorem`; \
           either replace `proof_wanted` with `theorem`, or reference another `proof_wanted` \
           via `❰…❱` in the statement or body"
    -- Class-valued wanted refs get instance binders so Lean's typeclass synth can use them
    -- (including via Π-instance synth when chained through another wanted). Non-class refs
    -- get implicit binders so the chained-dependency parameter can be unified at use sites.
    let extraBinders ← order.mapM fun (hyp, refInfo) =>
      if refInfo.isClass then
        `(Parser.Term.bracketedBinderF| [$hyp : $(refInfo.binderType)])
      else
        `(Parser.Term.bracketedBinderF| {$hyp : $(refInfo.binderType)})
    -- The `(_ : Prop)` ascription reproduces the "not a proposition" check `theorem` gives for
    -- free; `linter.unusedVariables` is silenced because user binders may only appear in the
    -- statement. The body, if present, is discharged via `have` so it is type-checked but
    -- discarded.
    match body'? with
    | none =>
      elabCommand <| ← `(
        section
        set_option linter.unusedVariables false
        private def $name $args* $extraBinders* : ProofWanted (($res' : Prop)) := ⟨⟩
        end)
    | some body' =>
      elabCommand <| ← `(
        section
        set_option linter.unusedVariables false
        private def $name $args* $extraBinders* : ProofWanted (($res' : Prop)) :=
          have : ($res' : Prop) := $body'
          ⟨⟩
        end)
  | _ => throwUnsupportedSyntax

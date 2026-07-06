/-
Copyright (c) 2023 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Thrane Christiansen, Kim Morrison
-/
module

public import Batteries.Tactic.Lint.Misc
public meta import Lean.Elab.Command
public meta import Lean.Meta.Tactic.TryThis -- shake: keep
import Lean.Parser.Command

/-!
# The `theorem_wanted`, `def_wanted`, and `instance_wanted` commands

Use `theorem_wanted name binders : T` to mark a theorem the library should eventually contain
without blocking compilation; `def_wanted name binders : T` does the same for any
`Sort`, not just `Prop`. Each elaborates to a private placeholder `def name binders : ProofWanted
T := ⟨⟩` (resp. `DefWanted T`), so the wanted result is visible to downstream files and
tools by type rather than by side-channel. `proof_wanted` is a synonym for `theorem_wanted`.

Inside any of these commands, `❰foo❱` references an earlier wanted declaration; for parametrised
`foo`, write `❰foo❱ x y` to apply it. The brackets desugar to fresh parameter binders, so the
dependency appears in the recorded type. When the referenced wanted's payload is a typeclass,
the generated parameter is an instance binder, so Lean's instance synth can pick it up at use
sites (including via Π-instance synth when chained through another wanted).

`instance_wanted name : ClassT` is a variant of `def_wanted` whose payload must be a
typeclass and whose declared name is registered file-locally: every later wanted automatically
picks up an `[…]` instance binder for it, without an explicit `❰…❱` reference.

A body may be supplied with `... := body`; it must reference at least one `❰…❱` (in the
statement or the body). A complete proof, construction, or instance should be a `theorem`,
`def`, or `instance` instead, and the error includes a `Try this:` suggestion to that effect.

The `❰` and `❱` characters (U+2770, U+2771) are entered as `\h<` and `\h>` with the standard
Lean input method.
-/

/-- Wrapper recording that a `proof_wanted` of statement `α` has been declared. -/
public structure ProofWanted (α : Sort u) : Type where
  /-- The trivial constructor; carries no information. -/
  mk ::

/-- Reducible accessor so a binder of type `ProofWanted.Stmt foo` reduces to `foo`'s
statement. Used by the desugaring of `❰foo❱` when `foo` is a `proof_wanted`. -/
@[reducible, nolint unusedArguments, expose]
public def ProofWanted.Stmt {α : Sort u} (_ : ProofWanted α) : Sort u := α

/-- Wrapper recording that a `def_wanted` of type `α` has been declared. -/
public structure DefWanted (α : Sort u) : Type where
  /-- The trivial constructor; carries no information. -/
  mk ::

/-- Reducible accessor so a binder of type `DefWanted.Val foo` reduces to `foo`'s
type. Used by the desugaring of `❰foo❱` when `foo` is a `def_wanted`. -/
@[reducible, nolint unusedArguments, expose]
public def DefWanted.Val {α : Sort u} (_ : DefWanted α) : Sort u := α

public meta section

open Lean Elab Command

/-- Internal bracket syntax `❰foo❱` for referencing an earlier `theorem_wanted` or
`def_wanted`. Only meaningful inside the statement or body of one of those commands;
the term elaborator errors everywhere else. -/
syntax (name := wantedRef) "❰" ident "❱" : term

/-- Elaborator that errors when `❰…❱` is used outside a wanted-declaration command. -/
@[term_elab wantedRef]
def elabWantedRef : Term.TermElab := fun _ _ =>
  throwError "`❰…❱` may only appear inside the statement or body of `theorem_wanted`, \
    `proof_wanted`, `def_wanted`, or `instance_wanted`"

/-- Which flavour of wanted-declaration a `❰foo❱` reference resolved to. The accessor and
binder-name prefix depend on the *referenced* declaration's kind, not the enclosing command's. -/
private inductive WantedRefKind
  | proofWanted
  | defWanted

/-- The accessor that reduces `<wrapper> foo` to `foo`'s recorded statement/type. -/
private def WantedRefKind.accessor : WantedRefKind → Name
  | .proofWanted        => ``ProofWanted.Stmt
  | .defWanted => ``DefWanted.Val

/-- Prefix for the generated parameter binder name. -/
private def WantedRefKind.hypPrefix : WantedRefKind → String
  | .proofWanted        => "h_"
  | .defWanted => "d_"

/-- Configuration distinguishing the wanted commands at the elaborator level. -/
private structure WantedCmdKind where
  /-- Command keyword used in error messages, e.g. `theorem_wanted`. -/
  cmdName : String
  /-- Wrapper constant emitted in the placeholder, e.g. ``ProofWanted``. -/
  wrapper : Name
  /-- If `true`, the recorded statement must be a `Prop` (the placeholder is ascribed `: Prop`,
  and `theorem` is used for the "Try this:" fallback). -/
  requireProp : Bool
  /-- If `true`, the wanted declaration is an `instance_wanted`: the recorded payload must
  be a typeclass, the `Try this:` fallback is `instance`, and the declared name is registered
  in `wantedInstancesExt` so subsequent wanted decls auto-include it. -/
  isInstance : Bool := false

/-- The keyword used in the `Try this:` suggestion and in the error message when a body has
no `❰…❱` reference. `instance_wanted` → `instance`, `theorem_wanted` / `proof_wanted` → `theorem`,
`def_wanted` → `def`. -/
private def WantedCmdKind.fallbackKeyword (kind : WantedCmdKind) : String :=
  if kind.isInstance then "instance"
  else if kind.requireProp then "theorem"
  else "def"

private def theoremWantedCmd : WantedCmdKind :=
  { cmdName := "theorem_wanted", wrapper := ``ProofWanted, requireProp := true }

/-- `proof_wanted` is a synonym for `theorem_wanted`; only the command keyword used in error
messages differs. -/
private def proofWantedCmd : WantedCmdKind :=
  { cmdName := "proof_wanted", wrapper := ``ProofWanted, requireProp := true }

private def defWantedCmd : WantedCmdKind :=
  { cmdName := "def_wanted", wrapper := ``DefWanted, requireProp := false }

private def instanceWantedCmd : WantedCmdKind :=
  { cmdName := "instance_wanted", wrapper := ``DefWanted, requireProp := false,
    isInstance := true }

/-- File-local registry of `instance_wanted` declarations. Each registered name is
automatically included as an instance parameter binder in every later wanted declaration's
signature, so Lean's typeclass synth can pick it up without an explicit `❰…❱` reference. The
extension is non-persistent across imports (the placeholder defs are `private` and don't
propagate). -/
private initialize wantedInstancesExt :
    SimplePersistentEnvExtension Name (Array Name) ←
  registerSimplePersistentEnvExtension {
    addEntryFn    := fun s n => s.push n
    addImportedFn := fun _ => #[]
  }

/-- Walk a syntax tree, throwing on the first `wantedRef` node found. -/
private def rejectRefsIn (loc : String) (cmdName : String) (stx : Syntax) : CommandElabM Unit := do
  let _ ← stx.replaceM fun s => do
    if s.getKind == ``wantedRef then
      throwErrorAt s "`❰…❱` may not appear inside {loc} of `{cmdName}`"
    return none

/-- Build a fresh parameter identifier name based on the last component of `n`, prefixed
according to the referenced kind (`h_` for `proof_wanted`, `d_` for `def_wanted`). -/
private def freshHypName (n : Name) (kind : WantedRefKind) : CommandElabM Name := do
  let baseStr := match n.componentsRev.head? with
    | some (.str _ s) => kind.hypPrefix ++ s
    | _ => kind.hypPrefix ++ "ref"
  liftCoreM <| Lean.mkFreshUserName (Name.mkSimple baseStr)

/-- Information returned by `classifyWantedRef`: the wrapper kind, the parameter-binder type
syntax to use when referencing it (a Π-type over `nm`'s own binders, ending in the appropriate
`.Stmt`/`.Val` accessor), and a flag saying whether the recorded payload is a typeclass — the
generated parameter is then an instance binder. -/
private structure WantedRefInfo where
  kind : WantedRefKind
  /-- The binder type, e.g. `ProofWanted.Stmt foo` for parameterless `foo`, or
  `∀ (n : Nat), (foo n).Stmt` if `foo` itself has binders. -/
  binderType : TSyntax `term
  /-- `true` if the wanted's payload is a typeclass. The generated parameter is then an instance
  binder so Lean's instance synth can find it. -/
  isClass : Bool

/-- Check that `nm` is a `theorem_wanted` or `def_wanted` declaration, and return both
which kind it is and the parameter-binder type to use when referencing it. The binder type is
Π-quantified over `nm`'s own binders, so parametrised wanted declarations can be referenced as
`❰foo❱ x y` (which desugars to applying the generated parameter to `x y`).

We build the binder type by combining explicit syntactic construction for the Π body (so that
`@foo` is applied to each binder's argument) with `PrettyPrinter.delab` for each binder's TYPE
(under options that force a round-trip-safe form). The arguments use fresh names rather than
those from `forallTelescope` to avoid hygiene collisions with the outer signature, and `@` is
prepended to each argument to suppress Lean's implicit-lambda / auto-application machinery —
otherwise functional arguments (e.g. a chained `d_Jacobian` binder) get η-expanded during
elaboration, leaving lambdas in the stored env type that don't round-trip back through delab. -/
private def classifyWantedRef (nm : Name) (stx : Syntax) : CommandElabM WantedRefInfo := do
  Command.liftTermElabM <| open Lean.Meta in do
    let info ← getConstInfo nm
    forallTelescope info.type fun fvars body => do
      -- Try to unify `body` with `wrapper ?α`; if it succeeds, return `?α` for any extra checks.
      let matchesWrapper (wrapper : Name) : MetaM (Option Expr) := do
        let u ← mkFreshLevelMVar
        let α ← mkFreshExprMVar (some (Lean.mkSort u))
        if ← isDefEq body (Lean.mkApp (Lean.mkConst wrapper [u]) α) then
          return some (← Lean.instantiateMVars α)
        return none
      let mkBinderSyn (refKind : WantedRefKind) : MetaM (TSyntax `term) := do
        let fooIdent := mkIdent nm
        -- Each universe level is a hole `_` rather than `nm`'s own level name: a named level would
        -- auto-bind to a fresh, distinct param of the enclosing declaration, leaving the hypothesis
        -- monomorphic at a universe that can never match the use site (e.g. referencing
        -- `exists_ulift.{w}` at universe `u`). A hole unifies with whatever universe the reference
        -- is used at. One reference at two different universes still can't be expressed by a single
        -- binder; see the `ulift`/`TODO` tests in `BatteriesTest/theorem_wanted.lean`.
        let levelStxs : Array (TSyntax `level) ←
          info.levelParams.toArray.mapM fun _ => `(level| _)
        let oldNames : Array Name ← fvars.mapM fun fvar => return (← fvar.fvarId!.getDecl).userName
        let freshNames : Array Name ← oldNames.mapM fun n => do
          let baseStr : String := match n.eraseMacroScopes.componentsRev.head? with
            | some (.str _ s) => s
            | _ => "arg"
          Lean.mkFreshUserName (Name.mkSimple baseStr)
        let renameMap : Std.HashMap Name Name :=
          oldNames.zip freshNames |>.foldl (fun m (o, n) => m.insert o n) {}
        let renameInTy (ty : TSyntax `term) : MetaM (TSyntax `term) := do
          return ⟨← ty.raw.replaceM fun s => do
            if s.isIdent then
              if let some n := renameMap[s.getId]? then return some (mkIdent n).raw
            return none⟩
        let argIdents : Array (TSyntax `term) ← freshNames.mapM fun n => do
          let id := mkIdent n
          `(@$id)
        let appliedSyn : TSyntax `term ←
          if levelStxs.isEmpty then
            `(@$fooIdent $argIdents*)
          else
            `(@$fooIdent:ident.{$levelStxs,*} $argIdents*)
        let accessorIdent := mkIdent refKind.accessor
        let bodySyn ← `($accessorIdent $appliedSyn)
        let mut binderTySyn := bodySyn
        for i in [0:fvars.size] do
          let idx := fvars.size - 1 - i
          let fvar := fvars[idx]!
          let decl ← fvar.fvarId!.getDecl
          let nameId := mkIdent freshNames[idx]!
          let typeSyn ← withOptions (fun o =>
              ((((o.setBool `pp.explicit true).setBool
                  `pp.fieldNotation false).setBool
                `pp.fieldNotation.generalized false).setBool
                `pp.deepTerms true).setBool
                `pp.proofs true) <|
            PrettyPrinter.delab decl.type
          let typeSyn ← renameInTy typeSyn
          binderTySyn ← match decl.binderInfo with
            | .default        => `(($nameId : $typeSyn) → $binderTySyn)
            | .implicit       => `({$nameId : $typeSyn} → $binderTySyn)
            | .strictImplicit => `(⦃$nameId : $typeSyn⦄ → $binderTySyn)
            | .instImplicit   => `([$nameId : $typeSyn] → $binderTySyn)
        return binderTySyn
      let env ← getEnv
      let isCls (α : Expr) : Bool := match α.getAppFn with
        | .const n _ => Lean.isClass env n
        | _ => false
      if let some α ← matchesWrapper ``ProofWanted then
        unless ← isProp α do
          throwErrorAt stx
            "`{stx}` is a `ProofWanted`, but its statement is not a proposition"
        return { kind := .proofWanted, binderType := ← mkBinderSyn .proofWanted,
                 isClass := isCls α }
      if let some β ← matchesWrapper ``DefWanted then
        return { kind := .defWanted, binderType := ← mkBinderSyn .defWanted,
                 isClass := isCls β }
      throwErrorAt stx
        "`{stx}` is not a `theorem_wanted`, `proof_wanted`, or `def_wanted` declaration \
         (its type doesn't end in `ProofWanted _` or `DefWanted _`)"

/-- Shared elaborator for `theorem_wanted` and `def_wanted`. Walks the statement and (if
present) the body, rewriting each `❰x❱` to a fresh parameter; the parameter's type uses the
accessor (`ProofWanted.Stmt` or `DefWanted.Val`) appropriate to `x`'s own kind. If the
body has no `❰…❱` reference anywhere, emits a "Try this:" suggesting `theorem` / `def`. -/
private def elabWanted (kind : WantedCmdKind) (stx : Syntax)
    (mods : TSyntax ``Lean.Parser.Command.declModifiers)
    (name : TSyntax ``Lean.Parser.Command.declId)
    (args : TSyntaxArray [`ident, `Lean.Parser.Term.hole, `Lean.Parser.Term.bracketedBinder])
    (res : TSyntax `term)
    (body? : Option (TSyntax `term)) : CommandElabM Unit := do
  for arg in args do
    rejectRefsIn "binder type" kind.cmdName arg.raw
  -- Brackets are deduplicated by referenced name across both the statement and the body, so
  -- repeated `❰x❱` references share one parameter binder.
  let nameToHypRef : IO.Ref (NameMap (TSyntax `ident)) ← IO.mkRef {}
  let hypOrderRef : IO.Ref (Array (TSyntax `ident × WantedRefInfo)) ← IO.mkRef #[]
  let rewriteRefs (s : Syntax) : CommandElabM Syntax := s.replaceM fun node => do
    unless node.getKind == ``wantedRef do return none
    let identStx : Syntax.Ident := ⟨node[1]⟩
    let nm ← liftCoreM <| Elab.realizeGlobalConstNoOverloadWithInfo identStx
    let m ← nameToHypRef.get
    match m.find? nm with
    | some h => return some h.raw
    | none =>
      let refInfo ← classifyWantedRef nm identStx
      let fresh ← freshHypName nm refInfo.kind
      let hyp : TSyntax `ident := mkIdent fresh
      nameToHypRef.set (m.insert nm hyp)
      hypOrderRef.modify (·.push (hyp, refInfo))
      return some hyp.raw
  let res' : TSyntax `term := ⟨← rewriteRefs res.raw⟩
  let body'? : Option (TSyntax `term) ← body?.mapM fun b => return ⟨← rewriteRefs b.raw⟩
  -- A body with no *user-written* `❰…❱` reference is a complete proof/construction/instance,
  -- and should use the corresponding native keyword. We snapshot `hypOrderRef` *before* the
  -- auto-include loop so ambient `instance_wanted` registrations don't accidentally satisfy
  -- this check.
  if let some body := body? then
    if (← hypOrderRef.get).isEmpty then
      let suggestionStx ← if kind.isInstance then
          -- `instance` uses `Term.attrKind` rather than `declModifiers`, so we drop modifiers
          -- in the suggestion. Users can re-add `@[…]` attributes manually if needed.
          `(command| instance $name:declId $args* : $res := $body)
        else if kind.requireProp then
          `(command| $mods:declModifiers theorem $name $args* : $res := $body)
        else
          `(command| $mods:declModifiers def $name $args* : $res := $body)
      liftCoreM <| Lean.Meta.Tactic.TryThis.addSuggestion stx
        { suggestion := .tsyntax suggestionStx }
      throwError
        "`{kind.cmdName}` with a body but no `❰…❱` reference is just a `{kind.fallbackKeyword}`; \
         either replace `{kind.cmdName}` with `{kind.fallbackKeyword}`, or reference another \
         `theorem_wanted` / `proof_wanted` / `def_wanted` / `instance_wanted` via `❰…❱` \
         in the statement or body"
  -- After user-written brackets have populated `nameToHypRef`, auto-include every registered
  -- `instance_wanted` not already referenced. The auto-includes come *after* user binders so
  -- their generated types can refer to identifiers introduced by user brackets.
  for instName in wantedInstancesExt.getState (← getEnv) do
    if (← nameToHypRef.get).contains instName then continue
    let refInfo ← classifyWantedRef instName stx
    let fresh ← freshHypName instName refInfo.kind
    let hyp : TSyntax `ident := mkIdent fresh
    nameToHypRef.modify (·.insert instName hyp)
    hypOrderRef.modify (·.push (hyp, refInfo))
  let order ← hypOrderRef.get
  -- Class-valued wanted refs become instance binders so Lean's typeclass synth can find them
  -- (including via Π-instance synth when chained through another wanted). Non-class refs become
  -- implicit binders, so the chained-dependency parameter is unified with the local one at use
  -- sites.
  let extraBinders ← order.mapM fun (hyp, refInfo) =>
    if refInfo.isClass then
      `(Parser.Term.bracketedBinderF| [$hyp : $(refInfo.binderType)])
    else
      `(Parser.Term.bracketedBinderF| {$hyp : $(refInfo.binderType)})
  -- For `proof_wanted` the `(_ : Prop)` ascription reproduces the "not a proposition" check
  -- `theorem` gives for free; `def_wanted` omits it. `linter.unusedVariables` is
  -- silenced because user binders may only appear in the statement. With a body, the discarded
  -- `have` type-checks `body'` against the statement without preserving it as a proof.
  let wrapper : TSyntax `ident := mkIdent kind.wrapper
  let resAscribed : TSyntax `term ← if kind.requireProp then `(($res' : Prop)) else `($res')
  let rhs : TSyntax `term ← match body'? with
    | none => `(⟨⟩)
    | some body' => `(have : $resAscribed := $body'; ⟨⟩)
  elabCommand <| ← `(
    section
    set_option linter.unusedVariables false
    private def $name $args* $extraBinders* : $wrapper $resAscribed := $rhs
    end)

/-- This proof would be a welcome contribution to the library!

The syntax of `theorem_wanted` declarations is just like that of `theorem`. Without `:=` and a
proof body it records a wanted theorem; with one it records a partial proof that still depends on
other wanted lemmas. Lean checks that `theorem_wanted` declarations are well-formed (e.g. it
ensures that all the mentioned names are in scope, and that the theorem statement is a valid
proposition), and records a private placeholder declaration of type `... → ProofWanted statement`.

Modifiers (such as `@[simp]`) are accepted for syntactic compatibility with `theorem` but are
currently ignored.

`proof_wanted` is a synonym for `theorem_wanted`.

Inside another `theorem_wanted` or `def_wanted`, write `❰foo❱` to reference an earlier
`theorem_wanted` or `def_wanted` named `foo`. The bracket may appear in the statement or
the body, and each distinct reference becomes a fresh parameter binder of the matching type. For
parametrised `foo : ∀ args, ProofWanted _`, the binder type is itself Π-quantified, so `❰foo❱ x
y` applies the parameter to `x y`. `❰foo❱` only resolves names within the current file, since
the placeholders are `private`.

A body must reference at least one `❰…❱` (in the statement or the body); otherwise the body is
a complete proof and the declaration should be a `theorem`.

Typical usage:
```
-- A parameterless wanted fact:
theorem_wanted size_of_two_pushes_onto_empty :
    ((#[] : Array Nat).push 1 |>.push 2).size = 2

-- Referencing an earlier `theorem_wanted` inside a statement (here in the `Fin`
-- bound proof, which rewrites by the wanted fact):
theorem_wanted first_index_after_two_pushes :
    (⟨0, by rw [❰size_of_two_pushes_onto_empty❱]; decide⟩
      : Fin ((#[] : Array Nat).push 1 |>.push 2).size).val = 0

-- A parametrised wanted fact:
theorem_wanted size_after_two_pushes {α : Type _} (a : Array α) (x y : α) :
    ((a.push x).push y).size = a.size + 2

-- Referencing the parametrised wanted with arguments: `❰foo❱ a x y`.
theorem_wanted index_after_two_pushes {α : Type _} (a : Array α) (x y : α) :
    (⟨a.size, by rw [❰size_after_two_pushes❱ a x y]; omega⟩
      : Fin ((a.push x).push y).size).val = a.size

-- A partial proof may be supplied with `:= body`, deferring the harder step via `❰…❱`:
theorem_wanted size_after_three_pushes {α : Type _} (a : Array α) (x y z : α) :
    (((a.push x).push y).push z).size = a.size + 3 := by
  rw [Array.size_push, ❰size_after_two_pushes❱ a x y]
```
-/
@[command_parser]
def «theorem_wanted» := leading_parser
  Parser.Command.declModifiers false >> "theorem_wanted" >>
    Parser.Command.declId >> Parser.ppIndent Parser.Command.declSig >>
    Parser.optional (" := " >> Parser.termParser)

/-- `proof_wanted` is a synonym for `theorem_wanted`; see its documentation. (It is expected to be
deprecated in favour of `theorem_wanted` eventually.) -/
@[command_parser]
def «proof_wanted» := leading_parser
  Parser.Command.declModifiers false >> "proof_wanted" >>
    Parser.Command.declId >> Parser.ppIndent Parser.Command.declSig >>
    Parser.optional (" := " >> Parser.termParser)

/-- This construction would be a welcome contribution to the library!

The syntax mirrors `theorem_wanted` but admits any `Sort` (not just `Prop`). It records a
placeholder declaration of type `... → DefWanted type` and accepts the same `❰…❱`
bracket syntax for cross-referencing earlier `theorem_wanted` or `def_wanted`
declarations, including parametrised ones — `❰foo❱ x y` applies `foo`'s parameters. A partial
body may be supplied with `... := body`; as with `theorem_wanted`, a body without any `❰…❱`
reference is rejected with an actionable "Try this:" suggesting `def`.

Modifiers (such as `@[simp]`) are accepted for syntactic compatibility with `def` but are
currently ignored.

Typical usage:
```
def_wanted decision_procedure (n : Nat) : Decidable (Nat.Prime n)

def_wanted prime_dec_3 : Decidable (Nat.Prime 3) := ❰decision_procedure❱ 3
```
-/
@[command_parser]
def «def_wanted» := leading_parser
  Parser.Command.declModifiers false >> "def_wanted" >>
    Parser.Command.declId >> Parser.ppIndent Parser.Command.declSig >>
    Parser.optional (" := " >> Parser.termParser)

/-- Parses the surface syntax of `theorem_wanted` and forwards to the shared `elabWanted`. -/
@[command_elab «theorem_wanted»]
def elabTheoremWanted : CommandElab := fun stx => do
  match stx with
  | `($mods:declModifiers theorem_wanted $name $args* : $res $[:= $body?]?) =>
    elabWanted theoremWantedCmd stx mods name args res body?
  | _ => throwUnsupportedSyntax

/-- Parses the surface syntax of `proof_wanted` (a synonym for `theorem_wanted`) and forwards to
the shared `elabWanted`. -/
@[command_elab «proof_wanted»]
def elabProofWanted : CommandElab := fun stx => do
  match stx with
  | `($mods:declModifiers proof_wanted $name $args* : $res $[:= $body?]?) =>
    elabWanted proofWantedCmd stx mods name args res body?
  | _ => throwUnsupportedSyntax

/-- Parses the surface syntax of `def_wanted` and forwards to the shared `elabWanted`. -/
@[command_elab «def_wanted»]
def elabDefWanted : CommandElab := fun stx => do
  match stx with
  | `($mods:declModifiers def_wanted $name $args* : $res $[:= $body?]?) =>
    elabWanted defWantedCmd stx mods name args res body?
  | _ => throwUnsupportedSyntax

/-- This typeclass instance would be a welcome contribution to the library!

The syntax mirrors `instance` (the name is optional, auto-generated from the class head if
absent) and the payload must be a typeclass. The placeholder is recorded as
`DefWanted (TheClass …)` like `def_wanted`, but additionally the declared
name is registered so every subsequent `theorem_wanted` / `def_wanted` /
`instance_wanted` automatically picks up a `[d_…]` instance binder for it. Lean's typeclass
synth then resolves uses of the class without an explicit `❰…❱` reference — matching the
auto-availability of regular `instance` declarations.

The registration is **module-scoped and order-sensitive**: every `instance_wanted` declared
earlier in the current file is auto-included as a binder on every later wanted declaration
(without any class-name filtering — opting in via `instance_wanted` is taken as a request for
the instance to be ambient). Registrations persist across `section` / `namespace` boundaries
within the file and are dropped at module boundaries (the placeholder defs are `private`, so
nothing propagates to importers).

Typical usage:
```
def_wanted Jacobian (C : Over (Spec (.of k))) [IsProper C.hom] : Over (Spec (.of k))

instance_wanted : GrpObj (❰Jacobian❱ C)

theorem_wanted comp_ofCurve … : … = η[❰Jacobian❱ C]
  -- automatically picks up the GrpObj instance, no haveI needed
```
-/
@[command_parser]
def «instance_wanted» := leading_parser
  Parser.Command.declModifiers false >> "instance_wanted" >>
    Parser.optional (Parser.ppSpace >> Parser.Command.declId) >>
    Parser.ppIndent Parser.Command.declSig >>
    Parser.optional (" := " >> Parser.termParser)

/-- Auto-generate a `declId` for an anonymous `instance_wanted` based on the class head of the
result type. Returns `inst<HeadName>` if free in the current namespace, otherwise
`inst<HeadName>_1`, `inst<HeadName>_2`, … — matching Lean's own anonymous-`instance` naming
style and keeping the name user-resolvable (no macro-scope hygiene suffix). -/
private def autoInstanceWantedName (stx : Syntax) (res : TSyntax `term) :
    CommandElabM (TSyntax ``Lean.Parser.Command.declId) := do
  let headStr : String :=
    if let some atom := res.raw.find? fun s => s.isIdent then
      match atom.getId with
      | .str _ s => s
      | _ => "wanted"
    else "wanted"
  let env ← getEnv
  let ns ← getCurrNamespace
  let base := "inst" ++ headStr
  -- `instance_wanted`'s underlying `private def` is name-mangled in the env, so a plain
  -- `env.contains` against the user-visible name misses it. Check the private form too.
  let isFree (s : String) : Bool :=
    let n := ns ++ Name.mkSimple s
    !env.contains n && !env.contains (Lean.mkPrivateName env n)
  let chosen :=
    if isFree base then base
    else Id.run do
      for n in [1:10000] do
        let s := s!"{base}_{n}"
        if isFree s then return s
      base  -- absurd fallback
  let ident : Ident := mkIdent (Name.mkSimple chosen)
  withRef stx `(Parser.Command.declId| $ident:ident)

/-- Parses the surface syntax of `instance_wanted`, generates a name if absent, forwards to the
shared `elabWanted`, validates the payload is a typeclass, and registers the declared name in
`wantedInstancesExt` so subsequent wanted declarations auto-include it. -/
@[command_elab «instance_wanted»]
def elabInstanceWanted : CommandElab := fun stx => do
  match stx with
  | `($mods:declModifiers instance_wanted $[$name?:declId]? $args* : $res $[:= $body?]?) => do
    let name ← match name? with
      | some n => pure n
      | none   => autoInstanceWantedName stx res
    elabWanted instanceWantedCmd stx mods name args res body?
    -- After elaboration, verify the payload is a typeclass and register the name. We look up
    -- the emitted private def via `classifyWantedRef` (which class-detects) using the resolved
    -- name from `declId`.
    let identStx : Syntax.Ident := ⟨name.raw[0]⟩
    let declName ← Command.liftTermElabM do
      Lean.Elab.realizeGlobalConstNoOverloadWithInfo identStx
    let refInfo ← classifyWantedRef declName name
    unless refInfo.isClass do
      throwErrorAt res
        "`instance_wanted` requires a typeclass payload; use `def_wanted` for \
         non-class data"
    modifyEnv (wantedInstancesExt.addEntry · declName)
  | _ => throwUnsupportedSyntax

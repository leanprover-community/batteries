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
# The `theorem_wanted`, `def_wanted`, and `instance_wanted` commands

Use `theorem_wanted name binders : T` to mark a theorem the library should eventually contain
without blocking compilation; `def_wanted name binders : T` does the same for any
`Sort`, not just `Prop`. Each elaborates to a private placeholder `def name binders : ProofWanted
T := ⟨⟩` (resp. `DefWanted T`), so the wanted result is visible to downstream files and
tools by type rather than by side-channel. `proof_wanted` is a synonym for `theorem_wanted`.

Inside any of these commands, `❰foo❱` references an earlier wanted declaration; for parametrised
`foo`, write `❰foo❱ x y` to apply it. When the referenced wanted's payload is a typeclass, the
generated parameter is an instance binder, so Lean's instance synth can pick it up at use sites
(including via Π-instance synth when chained through another wanted).

A body may be supplied with `... := body`; it must reference at least one `❰…❱` (in the statement or
the body). A complete proof, construction, or instance should be a `theorem`, `def`, or `instance`
instead, and the error includes a `Try this:` suggestion to that effect.

There are two flavours of wanted declaration:

* **Opaque holes** — a bodyless `def_wanted`/`theorem_wanted`/`instance_wanted` (and any
  `theorem_wanted`/`proof_wanted`/`instance_wanted`, with or without a body). These elaborate to a
  private placeholder `def foo binders : DefWanted T := ⟨⟩` (resp. `ProofWanted T`). A `❰foo❱`
  reference desugars to a fresh parameter binder of type `DefWanted.Val (@foo …)` (resp. `.Stmt`),
  so `foo` appears in the recorded type but is never inhabited.
* **Transparent (derived) defs** — a `def_wanted` *with a body*. This elaborates to a genuine
  `@[reducible] def foo binders : DerivedWanted T := ⟨body⟩`, and `❰foo❱` *inlines* it (projecting
  the carried value with `.val`), so `❰foo❱` is definitionally equal to `body`. This lets you build
  honest accessors and derived data on top of opaque holes — e.g. project a field out of a bundled
  wanted, with the projection actually reducing downstream — while the `DerivedWanted` wrapper keeps
  the declaration from being used directly as a value of `T` (only `❰…❱` accesses it).

Either way, a `❰foo❱` reference surfaces `foo`'s own transitive *leaf*-hole dependencies as binders
on the referencing declaration, threading them through; opaque holes stay as `d_…`/`h_…` binders,
transparent intermediates are inlined away. Because the only un-filled pieces are opaque
`DefWanted`/`ProofWanted` placeholders (never `axiom`/`sorry`), the whole construction is sound: a
transparent def is a real definition *parametrised over* its hypothetical leaves.

`instance_wanted name : ClassT` is a variant of `def_wanted` whose payload must be a typeclass and
whose declared name is registered file-locally, so a later wanted can use it via typeclass synth
without an explicit `❰…❱` reference. Inclusion is *on use* (like `variable [inst]`): a later
declaration carries the instance binder only when its statement or body actually needs it, not
unconditionally. (It is always an opaque hole, even with a body.)

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

/-- Wrapper carrying the body of a *transparent* `def_wanted` (one given a `:= body`). Unlike the
empty `DefWanted`, it stores the value, so `❰foo❱` projects it back out and downstream definitional
equalities go through; but the placeholder still has type `DerivedWanted T`, not `T`, so it cannot be
used directly as an inhabitant of `T` — the intended access is via the `❰…❱` syntax, which projects
the value back out. (`val` is `public`, so direct projection is possible, but `❰…❱` is what callers
should use.) -/
public structure DerivedWanted (α : Sort u) : Sort (max 1 u) where
  ofVal ::
  /-- The carried value. Reference the declaration via `❰…❱` rather than projecting this directly. -/
  val : α

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

/-- File-local registry recording, for each wanted declaration, how many of its trailing binders
are auto-generated (chained `❰…❱` references and ambient `instance_wanted` includes) rather than
user-written. A `❰foo❱` reference uses this to tell `foo`'s user binders (which it re-quantifies)
apart from `foo`'s own dependency binders (which it surfaces onto the enclosing declaration; see
`classifyWantedRef`). Non-persistent across imports, like `wantedInstancesExt`. -/
private initialize wantedArityExt :
    SimplePersistentEnvExtension (Name × Nat) (NameMap Nat) ←
  registerSimplePersistentEnvExtension {
    addEntryFn    := fun m (n, k) => m.insert n k
    addImportedFn := fun _ => {}
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

/-- A non-class dependency of the referenced wanted that must be surfaced as a binder on the
*enclosing* declaration (rather than quantified inside the reference's own binder, where it would
be an unsolvable implicit), then threaded into the reference's application. -/
private structure WantedDep where
  /-- The wanted declaration this dependency stands for; used to deduplicate against other
  references made by the enclosing declaration. -/
  name : Name
  /-- Fresh identifier naming the surfaced binder. Also spliced into the referenced wanted's
  application, so the dependency is passed through. -/
  ident : TSyntax `ident
  /-- The surfaced binder's type (Π over the dependency's own binders, ending in its accessor). -/
  binderType : TSyntax `term
  /-- Whether the surfaced binder is class-valued, so it becomes an instance binder `[…]` on the
  enclosing declaration (rather than implicit `{…}`). Only ever `true` for the leaf holes of a
  *transparent* reference, where every hole — class-valued or not — must be threaded explicitly into
  the inlined application; the opaque path keeps class deps quantified inside the `.Val` binder. -/
  isClass : Bool := false

/-- Information returned by `classifyWantedRef`: the wrapper kind, the parameter-binder type
syntax to use when referencing it (a Π-type over `nm`'s user binders, ending in the appropriate
`.Stmt`/`.Val` accessor), a flag saying whether the recorded payload is a typeclass — the
generated parameter is then an instance binder — and the non-class dependencies to surface. -/
private structure WantedRefInfo where
  kind : WantedRefKind
  /-- The binder type, e.g. `ProofWanted.Stmt foo` for parameterless `foo`, or
  `∀ (n : Nat), (foo n).Stmt` if `foo` itself has binders. -/
  binderType : TSyntax `term
  /-- `true` if the wanted's payload is a typeclass. The generated parameter is then an instance
  binder so Lean's instance synth can find it. -/
  isClass : Bool
  /-- `nm`'s own non-class wanted-dependencies, to be surfaced as binders on the enclosing
  declaration and threaded into `nm`'s application. Empty unless `nm` was itself declared with a
  body (or other `❰…❱` references) introducing chained dependencies. -/
  deps : Array WantedDep := #[]
  /-- For a *transparent* (derived) `nm`, the inlined replacement term: `nm` applied to its user
  arguments and to all of its surfaced leaf-hole binders, η-abstracted over the user arguments so
  that `❰nm❱ x y` βι-reduces to `nm`'s body. When `some`, `rewriteRefs` splices this in directly and
  adds no `d_nm` binder (`nm` is not a hole); `binderType`/`isClass`/`kind` are then unused. -/
  transparent : Option (TSyntax `term) := none

/-- Check that `nm` is a `theorem_wanted` or `def_wanted` declaration, and return both
which kind it is and the parameter-binder type to use when referencing it. The binder type is
Π-quantified over `nm`'s user binders, so parametrised wanted declarations can be referenced as
`❰foo❱ x y` (which desugars to applying the generated parameter to `x y`).

`nm`'s own auto-generated binders (chained `❰…❱` dependencies and ambient `instance_wanted`
includes — the trailing ones, counted by `wantedArityExt`) are handled specially. Instance-valued
ones stay quantified inside the reference's binder, so instance synth still discharges them at the
use site.
Non-class ones (a `def_wanted`/`theorem_wanted` `nm` referenced in its own body) would become
*unsolvable* implicits if quantified — nothing constrains them, since the `.Val`/`.Stmt` accessor
discards its argument — so instead they are returned as `deps`: the caller adds a matching binder
to the enclosing declaration and threads it into `nm`'s application.

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
    -- How many of `nm`'s trailing binders are auto-generated (vs user-written).
    let numAuto := (wantedArityExt.getState (← getEnv)).find? nm |>.getD 0
    forallTelescope info.type fun fvars body => do
      if numAuto > fvars.size then
        throwError "internal: wanted `{nm}` records {numAuto} auto binders but has only \
          {fvars.size} binders"
      let userCount := fvars.size - numAuto
      -- Recover the referenced wanted and its kind from an auto binder's type
      -- `∀ …, ProofWanted.Stmt (@ref …)` / `… DefWanted.Val (@ref …)`.
      -- Non-reducing telescope: the body is `ProofWanted.Stmt (@ref …)` / `DefWanted.Val (@ref …)`
      -- with the (reducible) accessor intact, so we can read off the accessor and referenced name.
      let classifyAutoBinder (ty : Expr) : MetaM (Name × WantedRefKind) :=
        forallTelescope ty fun _ b => do
          let some accName := b.getAppFn.constName?
            | throwError "internal: malformed wanted dependency binder `{ty}`"
          let some refName := b.appArg!.getAppFn.constName?
            | throwError "internal: malformed wanted dependency binder `{ty}`"
          let kind ← if accName == ``ProofWanted.Stmt then pure .proofWanted
            else if accName == ``DefWanted.Val then pure .defWanted
            else throwError "internal: malformed wanted dependency binder `{ty}`"
          return (refName, kind)
      -- Try to unify `body` with `wrapper ?α`; if it succeeds, return `?α` for any extra checks.
      let matchesWrapper (wrapper : Name) : MetaM (Option Expr) := do
        let u ← mkFreshLevelMVar
        let α ← mkFreshExprMVar (some (Lean.mkSort u))
        if ← isDefEq body (Lean.mkApp (Lean.mkConst wrapper [u]) α) then
          return some (← Lean.instantiateMVars α)
        return none
      -- Shared builder for both reference flavours. The opaque path (`mkBinderSyn`) produces a *Π*
      -- binder type `∀ userargs, accessor (@nm args)`; the transparent path (`mkTransparentRef`)
      -- produces a *λ* term `fun userargs => (@nm args).val`. Everything else is identical, so they
      -- differ only in `mkHead` (how the applied `@nm` is turned into the reference's core) and `pi`
      -- (whether the user binders are quantified as a Π or abstracted as a λ). Keeping this in one
      -- place is what guarantees both flavours get the same `delabTy` — in particular the universe
      -- rewrite below, whose omission from a duplicated transparent copy was a real bug.
      let buildRef (mkHead : TSyntax `term → MetaM (TSyntax `term)) (pi : Bool) :
          MetaM (TSyntax `term × Array WantedDep) := do
        let fooIdent := mkIdent nm
        -- Each universe level is a hole `_` rather than `nm`'s own level name: a named level would
        -- auto-bind to a fresh, distinct param of the enclosing declaration, leaving the reference
        -- monomorphic at a universe that can never match the use site (e.g. referencing
        -- `exists_ulift.{w}` at universe `u`, or `❰foo❱ ℚ` at a concrete universe). A hole unifies
        -- with whatever universe the reference is used at. One reference at two different universes
        -- still can't be expressed by a single binder; see the `ulift`/`TODO` tests in
        -- `BatteriesTest/theorem_wanted.lean`.
        let levelStxs : Array (TSyntax `level) ←
          info.levelParams.toArray.mapM fun _ => `(level| _)
        let oldNames : Array Name ← fvars.mapM fun fvar => return (← fvar.fvarId!.getDecl).userName
        let freshNames : Array Name ← oldNames.mapM fun n => do
          let baseStr : String := match n.eraseMacroScopes.componentsRev.head? with
            | some (.str _ s) => s
            | _ => "arg"
          Lean.mkFreshUserName (Name.mkSimple baseStr)
        -- `nm`'s auto-generated binders (indices `≥ userCount`) are all *surfaced* as flat `deps` —
        -- including instance-valued ones (the ambient `instance_wanted` includes) — rather than
        -- leaving the class ones quantified inside the reference. Quantifying them nests `nm`'s
        -- transitive instance binders into the generated type, which compounds super-exponentially
        -- across a chain of `instance_wanted`s (each includes all earlier ones); surfacing + dedup
        -- keeps the binders flat and linear. We allocate the per-argument identifier for every binder
        -- *before* delaborating any type, because an auto binder's type may reference an earlier
        -- surfaced binder — that reference must resolve to the placeholder we add to the enclosing
        -- declaration, not to `nm`'s internal name.
        let mut appNames : Array Name := freshNames
        let mut surfaced : Array (Nat × Name) := #[]  -- (binder index, referenced wanted)
        for idx in [userCount:fvars.size] do
          let (refName, refK) ← classifyAutoBinder (← fvars[idx]!.fvarId!.getDecl).type
          let baseStr : String := match refName.eraseMacroScopes.componentsRev.head? with
            | some (.str _ s) => refK.hypPrefix ++ s
            | _ => refK.hypPrefix ++ "ref"
          appNames := appNames.set! idx (← Lean.mkFreshUserName (Name.mkSimple baseStr))
          surfaced := surfaced.push (idx, refName)
        let renameMap : Std.HashMap Name Name :=
          oldNames.zip appNames |>.foldl (fun m (o, n) => m.insert o n) {}
        -- Delaborate a binder type to round-trip-safe syntax, renaming `nm`'s binders to the fresh
        -- names and rewriting `nm`'s universe parameters (which appear as named levels, e.g.
        -- `Type u_1`) to level holes `_` so the reference resolves at the use site's universe.
        let delabTy (ty : Expr) : MetaM (TSyntax `term) := do
          let s ← withOptions (fun o =>
              ((((o.setBool `pp.explicit true).setBool
                  `pp.fieldNotation false).setBool
                `pp.fieldNotation.generalized false).setBool
                `pp.deepTerms true).setBool
                `pp.proofs true) <|
            PrettyPrinter.delab ty
          return ⟨← s.raw.replaceM fun s => do
            if s.isIdent then
              if let some n := renameMap[s.getId]? then return some (mkIdent n).raw
              if info.levelParams.contains s.getId.eraseMacroScopes then
                return some (← `(level| _)).raw
            return none⟩
        let deps : Array WantedDep ← surfaced.mapM fun (idx, refName) => do
          let decl ← fvars[idx]!.fvarId!.getDecl
          return { name := refName, ident := mkIdent appNames[idx]!,
                   binderType := ← delabTy decl.type,
                   isClass := decl.binderInfo == .instImplicit }
        let argIdents : Array (TSyntax `term) ← appNames.mapM fun n => `(@$(mkIdent n))
        let appliedSyn : TSyntax `term ←
          if levelStxs.isEmpty then `(@$fooIdent $argIdents*)
          else `(@$fooIdent:ident.{$levelStxs,*} $argIdents*)
        -- Wrap the head in the user binders (indices `[0:userCount]`; the surfaced auto binders are
        -- threaded into `appliedSyn` instead), outermost first, as a Π or λ per `pi`.
        let mut acc ← mkHead appliedSyn
        for i in [0:userCount] do
          let idx := userCount - 1 - i
          let decl ← fvars[idx]!.fvarId!.getDecl
          let nameId := mkIdent freshNames[idx]!
          let typeSyn ← delabTy decl.type
          acc ← if pi then
            match decl.binderInfo with
            | .default        => `(($nameId : $typeSyn) → $acc)
            | .implicit       => `({$nameId : $typeSyn} → $acc)
            | .strictImplicit => `(⦃$nameId : $typeSyn⦄ → $acc)
            | .instImplicit   => `([$nameId : $typeSyn] → $acc)
          else
            match decl.binderInfo with
            | .default        => `(fun ($nameId : $typeSyn) => $acc)
            | .implicit       => `(fun {$nameId : $typeSyn} => $acc)
            | .strictImplicit => `(fun ⦃$nameId : $typeSyn⦄ => $acc)
            | .instImplicit   => `(fun [$nameId : $typeSyn] => $acc)
        return (acc, deps)
      -- Opaque reference: a `d_nm`/`h_nm` hypothesis of Π type `∀ userargs, accessor (@nm args)`.
      let mkBinderSyn (refKind : WantedRefKind) : MetaM (TSyntax `term × Array WantedDep) :=
        buildRef (fun core => `($(mkIdent refKind.accessor) $core)) (pi := true)
      -- Transparent reference (`def_wanted` with a body): inline `nm` itself, projecting the carried
      -- value out of the `DerivedWanted` wrapper with `.val`. With `nm` `@[reducible]`,
      -- `(@nm … leafholes).val` βιδ-reduces to `nm`'s body, so `❰nm❱` is definitionally that body.
      -- No `d_nm` binder is introduced — `nm` is not a hole; only its surfaced leaf holes are.
      let mkTransparentRef : MetaM (TSyntax `term × Array WantedDep) :=
        buildRef (fun core => `(($core).val)) (pi := false)
      if let some _ ← matchesWrapper ``DerivedWanted then
        let (term, deps) ← mkTransparentRef
        return { kind := .defWanted, binderType := term, isClass := false, deps,
                 transparent := some term }
      let env ← getEnv
      let isCls (α : Expr) : Bool := match α.getAppFn with
        | .const n _ => Lean.isClass env n
        | _ => false
      if let some α ← matchesWrapper ``ProofWanted then
        unless ← isProp α do
          throwErrorAt stx
            "`{stx}` is a `ProofWanted`, but its statement is not a proposition"
        let (binderType, deps) ← mkBinderSyn .proofWanted
        return { kind := .proofWanted, binderType, isClass := isCls α, deps }
      if let some β ← matchesWrapper ``DefWanted then
        let (binderType, deps) ← mkBinderSyn .defWanted
        return { kind := .defWanted, binderType, isClass := isCls β, deps }
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
  -- For transparent (derived) references, the replacement is an inlined *term*, not a `d_nm`
  -- binder; cache it by name so repeated `❰nm❱` references reuse the same splice.
  let transparentCache : IO.Ref (NameMap (TSyntax `term)) ← IO.mkRef {}
  -- Surface a reference's transitive leaf-hole dependencies as binders on this declaration (so they
  -- are solvable), deduplicating against binders already added; returns a renaming to apply to the
  -- reference's own binder type / inlined term, mapping each dep's fresh placeholder to the existing
  -- binder it coincides with. New deps are added *before* the reference's own binder, which refers to
  -- them. Used both for explicit `❰…❱` references and for ambient `instance_wanted` auto-includes —
  -- the latter previously skipped this, leaving an included instance's own deps (e.g. a shared
  -- `❰J❱`) referenced but unbound.
  let surfaceDeps (deps : Array WantedDep) :
      CommandElabM (TSyntax `term → CommandElabM (TSyntax `term)) := do
    let mut renames : Std.HashMap Name Name := {}
    for dep in deps do
      match (← nameToHypRef.get).find? dep.name with
      | some existing => renames := renames.insert dep.ident.getId existing.getId
      | none =>
        nameToHypRef.modify (·.insert dep.name dep.ident)
        hypOrderRef.modify (·.push (dep.ident,
          { kind := .defWanted, binderType := dep.binderType, isClass := dep.isClass }))
    return fun t => do
      if renames.isEmpty then return t
      return ⟨← t.raw.replaceM fun s => do
        if s.isIdent then
          if let some r := renames[s.getId]? then return some (mkIdent r).raw
        return none⟩
  let rewriteRefs (s : Syntax) : CommandElabM Syntax := s.replaceM fun node => do
    unless node.getKind == ``wantedRef do return none
    let identStx : Syntax.Ident := ⟨node[1]⟩
    let nm ← liftCoreM <| Elab.realizeGlobalConstNoOverloadWithInfo identStx
    if let some t := (← transparentCache.get).find? nm then return some t.raw
    match (← nameToHypRef.get).find? nm with
    | some h => return some h.raw
    | none =>
      let refInfo ← classifyWantedRef nm identStx
      let applyRenames ← surfaceDeps refInfo.deps
      match refInfo.transparent with
      | some term =>
        -- Transparent `nm`: inline the real `nm` applied to its surfaced leaf holes. No `d_nm`
        -- binder — `nm` is a genuine definition, not a hole.
        let term' ← applyRenames term
        transparentCache.modify (·.insert nm term')
        return some term'.raw
      | none =>
        let binderType ← applyRenames refInfo.binderType
        let fresh ← freshHypName nm refInfo.kind
        let hyp : TSyntax `ident := mkIdent fresh
        nameToHypRef.modify (·.insert nm hyp)
        hypOrderRef.modify (·.push (hyp, { refInfo with binderType }))
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
    -- Surface the ambient instance's *own* transitive deps too (deduped), so a dependency shared
    -- between several `instance_wanted`s (e.g. a common `❰J❱`) is bound once rather than left dangling.
    let applyRenames ← surfaceDeps refInfo.deps
    let binderType ← applyRenames refInfo.binderType
    let fresh ← freshHypName instName refInfo.kind
    let hyp : TSyntax `ident := mkIdent fresh
    nameToHypRef.modify (·.insert instName hyp)
    hypOrderRef.modify (·.push (hyp, { refInfo with binderType }))
  let order ← hypOrderRef.get
  -- Class-valued wanted refs become instance binders so Lean's typeclass synth can find them
  -- (including via Π-instance synth when chained through another wanted). Non-class refs become
  -- implicit binders; their own non-class dependencies have already been surfaced as sibling
  -- binders (see `rewriteRefs`) and threaded into the reference's application.
  let mkBinderStx : (TSyntax `ident × WantedRefInfo) →
      CommandElabM (TSyntax ``Lean.Parser.Term.bracketedBinder) := fun (hyp, refInfo) =>
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
  -- Emit the placeholder declaration with the given generated binders. A `def_wanted` *with a body*
  -- becomes a transparent `@[reducible]` def wrapped in `DerivedWanted`, so `❰foo❱` βι-reduces to its
  -- body and downstream definitional equalities go through; otherwise it is an opaque
  -- `DefWanted`/`ProofWanted` placeholder. The leaves it abstracts over remain opaque placeholders,
  -- so no `axiom`/`sorry` is introduced. (See the module docstring.)
  let emitDecl : Array (TSyntax ``Lean.Parser.Term.bracketedBinder) → CommandElabM Unit :=
    fun binders => do
      if body'?.isSome && !kind.requireProp && !kind.isInstance then
        let body' := body'?.get!
        -- `noncomputable`: a transparent placeholder may derive from noncomputable data (it is a
        -- blueprint, never compiled); the `@[reducible]` + `DerivedWanted` projection still unfold for
        -- definitional equality regardless.
        elabCommand <| ← `(
          section
          set_option linter.unusedVariables false
          @[reducible] private noncomputable def $name $args* $binders* : DerivedWanted $res' :=
            ⟨$body'⟩
          end)
      else
        let rhs : TSyntax `term ← match body'? with
          | none => `(⟨⟩)
          | some body' => `(have : $resAscribed := $body'; ⟨⟩)
        elabCommand <| ← `(
          section
          set_option linter.unusedVariables false
          private def $name $args* $binders* : $wrapper $resAscribed := $rhs
          end)
  -- Include-on-use: an ambient `instance_wanted` is otherwise bolted onto *every* later wanted, but a
  -- declaration should only carry the holes it actually needs (cf. `variable [inst]`). We emit with
  -- *all* generated binders, inspect the genuine elaborated declaration for the binders actually used
  -- (in its value or type, transitively through binders' own types), roll the emission back, and
  -- re-emit keeping only those. Using the real declaration elaboration — rather than a hand-rolled
  -- one — gets section variables, instance arguments, autobound implicits and universes right. Unused
  -- ambient instances (and any deps orphaned by their removal) are dropped, removing noise and the
  -- quadratic binder growth a chain of `instance_wanted`s used to cause. It is best effort: if the
  -- full emission fails (e.g. an intentional error-case test) we keep every binder so the final
  -- emission reports the canonical error.
  let allBinders ← order.mapM mkBinderStx
  let declId : Syntax.Ident := ⟨name.raw[0]⟩
  let keep : Array Bool ← if order.isEmpty then pure #[] else do
    let errCount (s : Command.State) : Nat :=
      (s.messages.toList.filter (·.severity == .error)).length
    let saved ← get
    let errsBefore := errCount saved
    -- Emit with *all* generated binders. `elabCommand` *logs* elaboration errors rather than
    -- throwing; if emitting with all binders errored (e.g. an intentional error-case test, or a body
    -- that genuinely fails to type-check), keep every binder and let the final emission report the
    -- canonical error. Otherwise the usage analysis below *must* succeed — a failure there is an
    -- internal bug and should surface, not silently degrade to "keep all" (which would mask exactly
    -- the regression include-on-use prevents).
    emitDecl allBinders
    let mask : Array Bool ←
      if errCount (← get) > errsBefore then
        pure (Array.replicate order.size true)
      else
        let nm ← Command.liftTermElabM <| Lean.Elab.realizeGlobalConstNoOverloadWithInfo declId
        let some val := (← getConstInfo nm).value?
          | throwError "internal: emitted wanted has no value"
        Command.liftTermElabM <| Lean.Meta.lambdaTelescope val fun fvars vbody => do
          let lctx ← getLCtx
          let collect (s : Std.HashSet FVarId) (e : Expr) : Std.HashSet FVarId :=
            (Lean.collectFVars {} e).fvarIds.foldl (·.insert ·) s
          let mut used : Std.HashSet FVarId := collect (collect {} vbody) (← Lean.Meta.inferType vbody)
          let mut changed := true
          while changed do
            changed := false
            for fv in used.toArray do
              if let some d := lctx.find? fv then
                for w in (Lean.collectFVars {} d.type).fvarIds do
                  unless used.contains w do used := used.insert w; changed := true
          let genStart := fvars.size - order.size
          return (Array.range order.size).map fun i => used.contains fvars[genStart + i]!.fvarId!
    -- Roll back the probe emission (and its messages) so only the final, pruned emission remains.
    set saved
    pure mask
  let order := (order.zip keep).filterMap fun (e, k) => if k then some e else none
  let extraBinders ← order.mapM mkBinderStx
  emitDecl extraBinders
  -- Record how many of this declaration's binders are auto-generated (`extraBinders`), so a later
  -- `❰…❱` reference can tell them apart from the user binders and surface the leaf holes. For a
  -- transparent declaration, also register it so references inline it instead of making a hole.
  let identStx : Syntax.Ident := ⟨name.raw[0]⟩
  let declName ← Command.liftTermElabM do
    Lean.Elab.realizeGlobalConstNoOverloadWithInfo identStx
  modifyEnv (wantedArityExt.addEntry · (declName, order.size))

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

The syntax mirrors `theorem_wanted` but admits any `Sort` (not just `Prop`). It accepts the same
`❰…❱` bracket syntax for cross-referencing earlier `theorem_wanted` or `def_wanted` declarations,
including parametrised ones — `❰foo❱ x y` applies `foo`'s parameters. A body without any `❰…❱`
reference is rejected with an actionable "Try this:" suggesting `def`.

A **bodyless** `def_wanted` records an opaque placeholder of type `... → DefWanted type` (a hole). A
`def_wanted` **with a body** is instead emitted as a genuine `@[reducible]` definition of type
`... → DerivedWanted type` (carrying the body), so `❰foo❱` inlines it and is definitionally equal to
its body — letting you derive honest accessors and data on top of opaque holes. The `DerivedWanted`
wrapper keeps it from being used directly as a value of `type`; only `❰…❱` accesses it. Either way no
`axiom`/`sorry` is introduced (see the module docstring).

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
`DefWanted (TheClass …)` like `def_wanted`, but additionally the declared name is registered so a
subsequent `theorem_wanted` / `def_wanted` / `instance_wanted` can use it via typeclass synth without
an explicit `❰…❱` reference — matching the auto-availability of regular `instance` declarations.

Inclusion is **on use** (like `variable [inst]`): a later declaration carries a `[d_…]` binder for an
earlier `instance_wanted` only when its statement or body actually uses it. A declaration that does
not need the instance does not carry it, so unrelated instances do not accumulate as a file grows.
The registration is **module-scoped and order-sensitive**: only `instance_wanted`s declared earlier
in the current file are candidates. Registrations persist across `section` / `namespace` boundaries
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

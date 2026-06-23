/-
Copyright (c) 2020 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Robert Y. Lewis, Arthur Paulino, Gabriel Ebner
-/
module

public meta import Lean.Util.CollectLevelParams
public meta import Lean.Util.ForEachExpr
public meta import Lean.Meta.Check
public meta import Lean.Meta.Instances
public meta import Lean.Util.Recognizers
public meta import Lean.DocString
public meta import Batteries.Tactic.Lint.Basic

public meta section

open Lean Meta Std

namespace Batteries.Tactic.Lint

/-!
# Various linters

This file defines several small linters.
-/

/-- A linter for checking whether a declaration has a namespace twice consecutively in its name. -/
@[env_linter] def dupNamespace : Linter where
  noErrorsFound := "No declarations have a duplicate namespace."
  errorsFound := "DUPLICATED NAMESPACES IN NAME:"
  test declName := do
    if ← isAutoDecl declName then return none
    if ← isImplicitReducible declName then return none
    let nm := declName.components
    let some (dup, _) := nm.zip nm.tail! |>.find? fun (x, y) => x == y
      | return none
    return m!"The namespace {dup} is duplicated in the name"

/-- A linter for checking for unused arguments. We skip all declarations that contain `sorry` in
their value, and allow arguments starting with `_` to be unused. -/
@[env_linter] def unusedArguments : Linter where
  noErrorsFound := "No unused arguments."
  errorsFound := "UNUSED ARGUMENTS."
  test declName := do
    if ← isAutoDecl declName then return none
    if ← isProjectionFn declName then return none
    let info ← getConstInfo declName
    let ty := info.type
    let some val := info.value? | return none
    if val.hasSorry || ty.hasSorry then return none
    forallTelescope ty fun args ty => do
      let mut e := (mkAppN val args).headBeta
      let ldecls ← args.mapM getFVarLocalDecl
      e := mkApp e ty
      for ldecl in ldecls do
        e := mkApp e ldecl.type
        if let some val := ldecl.value? then
          e := mkApp e val
      let unused := ldecls.zipIdx.filter fun (ldecl, _) =>
        !ldecl.userName.isInternal && !e.containsFVar ldecl.fvarId
      if unused.isEmpty then return none
      addMessageContextFull <| .joinSep (← unused.toList.mapM fun (ldecl, i) =>
          return m!"argument {i+1}: {ldecl.toExpr} : {ldecl.type}") m!", "

/-- A linter for checking definition doc strings. -/
@[env_linter] def docBlame : Linter where
  noErrorsFound := "No definitions are missing documentation."
  errorsFound := "DEFINITIONS ARE MISSING DOCUMENTATION STRINGS:"
  test declName := do
    -- leanprover/lean4#12263: isGlobalInstance was removed, use isInstance instead
    if (← isAutoDecl declName) || (← isInstance declName) then
      return none -- FIXME: scoped/local instances should also not be linted
    if let .str p _ := declName then
      if ← isInstance p then
        -- auxillary functions for instances should not be linted
        return none
    if let .str _ s := declName then
      if s == "parenthesizer" || s == "formatter" || s == "delaborator" || s == "quot" then
      return none
    let kind ← match ← getConstInfo declName with
      | .axiomInfo .. => pure "axiom"
      | .opaqueInfo .. => pure "constant"
      | .defnInfo info =>
          -- leanprover/lean4#2575: Prop projections are generated as `def`s
          if ← isProjectionFn declName <&&> isProp info.type then
            return none
          pure "definition"
      | .inductInfo .. => pure "inductive"
      | _ => return none
    let (none) ← findDocString? (← getEnv) declName | return none
    return m!"{kind} missing documentation string"

/-- A linter for checking theorem doc strings. -/
@[env_linter disabled] def docBlameThm : Linter where
  noErrorsFound := "No theorems are missing documentation."
  errorsFound := "THEOREMS ARE MISSING DOCUMENTATION STRINGS:"
  test declName := do
    if ← isAutoDecl declName then
      return none
    let kind ← match ← getConstInfo declName with
      | .thmInfo .. => pure "theorem"
      | .defnInfo info =>
          -- leanprover/lean4#2575:
          -- projections are generated as `def`s even when they should be `theorem`s
          if ← isProjectionFn declName <&&> isProp info.type then
            pure "Prop projection"
          else
            return none
      | _ => return none
    let (none) ← findDocString? (← getEnv) declName | return none
    return m!"{kind} missing documentation string"

/-- A linter for checking whether the correct declaration constructor (definition or theorem)
has been used. -/
@[env_linter] def defLemma : Linter where
  noErrorsFound := "All declarations correctly marked as def/lemma."
  errorsFound := "INCORRECT DEF/LEMMA:"
  test declName := do
    if (← isAutoDecl declName) || (← isImplicitReducible declName) then
      return none
    -- leanprover/lean4#2575:
    -- projections are generated as `def`s even when they should be `theorem`s
    if ← isProjectionFn declName then return none
    let info ← getConstInfo declName
    let isThm ← match info with
      | .defnInfo .. => pure false
      | .thmInfo .. => pure true
      | _ => return none
    match isThm, ← isProp info.type with
    | true, false => pure "is a lemma/theorem, should be a def"
    | false, true => pure "is a def, should be lemma/theorem"
    | _, _ => return none

/-- A linter for checking whether statements of declarations are well-typed.

This linter is disabled by default: declarations are already type-checked when added to the
environment, so re-checking every statement is redundant in normal use. As an alternative
defence-in-depth measure for catching kernel/elaborator bugs, prefer running an external
checker such as `lean4checker` or `trepplein`.
-/
@[env_linter disabled] def checkType : Linter where
  noErrorsFound :=
    "The statements of all declarations type-check with default reducibility settings."
  errorsFound := "THE STATEMENTS OF THE FOLLOWING DECLARATIONS DO NOT TYPE-CHECK."
  isFast := true
  test declName := do
    if ← isAutoDecl declName then return none
    if ← isTypeCorrect (← getConstInfo declName).type then return none
    return m!"the statement doesn't type check."

/-- A linter for checking that declarations aren't syntactic tautologies.
Checks whether a lemma is a declaration of the form `∀ a b ... z, e₁ = e₂`
where `e₁` and `e₂` are identical exprs.
We call declarations of this form syntactic tautologies.
Such lemmas are (mostly) useless and sometimes introduced unintentionally when proving basic facts
with rfl when elaboration results in a different term than the user intended. -/
@[env_linter] def synTaut : Linter where
  noErrorsFound :=
    "No declarations are syntactic tautologies."
  errorsFound := "THE FOLLOWING DECLARATIONS ARE SYNTACTIC TAUTOLOGIES. \
    This usually means that they are of the form `∀ a b ... z, e₁ = e₂` where `e₁` and `e₂` are \
    identical expressions. We call declarations of this form syntactic tautologies. \
    Such lemmas are (mostly) useless and sometimes introduced unintentionally when proving \
    basic facts using `rfl`, when elaboration results in a different term than the user intended. \
    You should check that the declaration really says what you think it does."
  isFast := true
  test declName := do
    if ← isAutoDecl declName then return none
    forallTelescope (← getConstInfo declName).type fun _ ty => do
      let some (lhs, rhs) := ty.eq?.map (fun (_, l, r) => (l, r)) <|> ty.iff?
        | return none
      if lhs == rhs then
        return m!"LHS equals RHS syntactically"
      return none

/--
Return a list of unused `let_fun` terms in an expression that introduce proofs.
-/
@[nolint unusedArguments]
def findUnusedHaves (_ : Expr) : MetaM (Array MessageData) := do
  -- adaptation note: kmill 2025-06-29. `Expr.letFun?` is deprecated.
  -- This linter needs to be updated for `Expr.letE (nondep := true)`, but it has false
  -- positives, so I am disabling it for now.
  return #[]
  /-
  let res ← IO.mkRef #[]
  forEachExpr e fun e => do
    match e.letFun? with
    | some (n, t, _, b) =>
      if n.isInternal then return
      if b.hasLooseBVars then return
      unless ← Meta.isProp t do return
      let msg ← addMessageContextFull m!"unnecessary have {n.eraseMacroScopes} : {t}"
      res.modify (·.push msg)
    | _ => return
  res.get
  -/

/-- A linter for checking that declarations don't have unused term mode have statements. -/
@[env_linter] def unusedHavesSuffices : Linter where
  noErrorsFound := "No declarations have unused term mode have statements."
  errorsFound := "THE FOLLOWING DECLARATIONS HAVE INEFFECTUAL TERM MODE HAVE/SUFFICES BLOCKS. \
    In the case of `have` this is a term of the form `have h := foo, bar` where `bar` does not \
    refer to `foo`. Such statements have no effect on the generated proof, and can just be \
    replaced by `bar`, in addition to being ineffectual, they may make unnecessary assumptions \
    in proofs appear as if they are used. \
    For `suffices` this is a term of the form `suffices h : foo, proof_of_goal, proof_of_foo` \
    where `proof_of_goal` does not refer to `foo`. \
    Such statements have no effect on the generated proof, and can just be replaced by \
    `proof_of_goal`, in addition to being ineffectual, they may make unnecessary assumptions \
    in proofs appear as if they are used."
  test declName := do
    if ← isAutoDecl declName then return none
    let info ← getConstInfo declName
    let mut unused ← findUnusedHaves info.type
    if let some value := info.value? then
      unused := unused ++ (← findUnusedHaves value)
    unless unused.isEmpty do
      return some <| .joinSep unused.toList ", "
    return none

/--
A linter for checking if variables appearing on both sides of an iff are explicit. Ideally, such
variables should be implicit instead.
-/
@[env_linter disabled] def explicitVarsOfIff : Linter where
  noErrorsFound := "No explicit variables on both sides of iff"
  errorsFound := "EXPLICIT VARIABLES ON BOTH SIDES OF IFF"
  test declName := do
    if ← isAutoDecl declName then return none
    forallTelescope (← getConstInfo declName).type fun args ty => do
      let some (lhs, rhs) := ty.iff? | return none
      let explicit ← args.filterM fun arg =>
        return (← getFVarLocalDecl arg).binderInfo.isExplicit &&
          lhs.containsFVar arg.fvarId! && rhs.containsFVar arg.fvarId!
      if explicit.isEmpty then return none
      addMessageContextFull m!"should be made implicit: {
        MessageData.joinSep (explicit.toList.map (m!"{·}")) ", "}"

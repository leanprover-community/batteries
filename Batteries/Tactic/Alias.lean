/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, David Renshaw, François G. Dorais
-/
module

public meta import Lean.Elab.Command
public meta import Lean.Elab.DeclarationRange
public meta import Lean.Compiler.NoncomputableAttr
public meta import Lean.DocString
public meta import Batteries.CodeAction.Deprecated

public meta section

/-!
# The `alias` command

The `alias` command is used to create synonyms. The plain command can create a synonym of any
declaration. There is also a version to create synonyms for the forward and reverse implications of
an iff theorem.
-/

namespace Batteries.Tactic.Alias

open Lean Elab Parser.Command

/-- An alias can be in one of three forms -/
inductive AliasInfo where
  /-- Plain alias -/
  | plain (n : Name)
  /-- Forward direction of an iff alias -/
  | forward (n : Name)
  /-- Reverse direction of an iff alias -/
  | reverse (n : Name)
deriving Inhabited

/-- The name underlying an alias target -/
def AliasInfo.name : AliasInfo → Name
  | plain n => n
  | forward n => n
  | reverse n => n

/-- The docstring for an alias. -/
def AliasInfo.toString : AliasInfo → String
  | plain n => s!"**Alias** of `{n}`."
  | forward n => s!"**Alias** of the forward direction of `{n}`."
  | reverse n => s!"**Alias** of the reverse direction of `{n}`."

/--
Add a docstring to the alias `declName` if it doesn't already have one.
This needs to run after elaboration of attributes, because e.g. `inherit_doc` could a add docstring.
This is also used in `to_additive`/`to_dual`.
-/
def addAliasDocstring (declName : Name) (info : AliasInfo) : CoreM Unit := do
  if (← findDocString? (← getEnv) declName).isNone then
    let mut doc := info.toString
    if let some origDoc ← findDocString? (← getEnv) info.name then
      doc := s!"{doc}\n\n---\n\n{origDoc}"
    addDocStringCore declName doc

/-- Environment extension for registering aliases -/
initialize aliasExt : MapDeclarationExtension AliasInfo ← mkMapDeclarationExtension

/-- Get the alias information for a name -/
def getAliasInfo?  [Monad m] [MonadEnv m] (name : Name) : m (Option AliasInfo) := do
  return aliasExt.find? (← getEnv) name

/-- Get the old alias information for a name. -/
partial def getOldAliasInfo? [Monad m] [MonadEnv m] (name : Name) : m (Option AliasInfo) := do
  match ← getAliasInfo? name with
  | some (.plain n) => getOldAliasInfo? n
  | some (.forward n) =>
    if let some (.plain n') ← getOldAliasInfo? n then
      return some (.forward n')
    else
      return some (.forward n)
  | some (.reverse n) =>
    if let some (.plain n') ← getOldAliasInfo? n then
      return some (.reverse n')
    else
      return some (.reverse n)
  | none => return none

/-- Get the alias information for a name -/
@[deprecated "use `getAliasInfo?` or `getOldAliasInfo?` for the original behavior"
  (since := "2026-04-11")]
def getAliasInfo [Monad m] [MonadEnv m] (name : Name) : m (Option AliasInfo) :=
  getOldAliasInfo? name

/-- Returns the path of aliases starting at a given name.

The return value is a pair `(mps, name)` where `name` is the final non-aliased name in the
alias chain and `mps` is a list of `Bool` indicating the sequence of forward (`true`) and
reverse (`false`) aliases along the chain.
-/
partial def getAliasPath [Monad m] [MonadEnv m] (name : Name) : m (List Bool × Name) := do
  match ← getAliasInfo? name with
  | some (.plain name) => getAliasPath name
  | some (.forward name) =>
    let (p, name) ← getAliasPath name
    return (true :: p, name)
  | some (.reverse name) =>
    let (p, name) ← getAliasPath name
    return (false :: p, name)
  | none => return ([], name)

/-- Set the alias info for a new declaration -/
def setAliasInfo [MonadEnv m] (info : AliasInfo) (declName : Name) : m Unit :=
  modifyEnv (aliasExt.insert · declName info)

/-- Updates the `deprecated` declaration to point to `target` if no target is provided. -/
def setDeprecatedTarget (target : Name) (arr : Array Attribute) : Array Attribute × Bool :=
  StateT.run (m := Id) (s := false) do
    arr.mapM fun s => do
      if s.name == `deprecated then
        if let `(deprecated| deprecated%$tk $[$desc:str]? $[(since := $since)]?) := s.stx then
          set true
          let stx := Unhygienic.run
            `(deprecated| deprecated%$tk $(mkCIdent target) $[$desc:str]? $[(since := $since)]?)
          pure { s with stx }
        else pure s
      else pure s

/-- Resolve `nameStx` for an alias, opening the alias name's namespace prefix (like `def`). -/
private def resolveAliasTarget (aliasId : Name) (nameStx : Ident) : TermElabM Name := do
  withoutExporting do
    let ns ←
      if (`_root_).isPrefixOf aliasId then
        pure (aliasId.replacePrefix `_root_ .anonymous).getPrefix
      else
        pure <| (← getCurrNamespace) ++ aliasId.getPrefix
    if ns.isAnonymous then
      realizeGlobalConstNoOverloadWithInfo nameStx
    else
      withTheReader Core.Context (fun ctx =>
          { ctx with openDecls := .simple ns [] :: ctx.openDecls }) do
        realizeGlobalConstNoOverloadWithInfo nameStx

/--
  The command `alias name := target` creates a synonym of `target` with the given name.

  The command `alias ⟨fwd, rev⟩ := target` creates synonyms for the forward and reverse directions
  of an iff theorem. Use `_` if only one direction is required.

  These commands accept all modifiers and attributes that `def` and `theorem` do.
 -/
elab (name := alias) mods:declModifiers "alias " alias:ident " := " nameStx:ident : command => do
  let scopeNoncomputable := (← Command.getScope).isNoncomputable
  let scopeMeta := (← Command.getScope).isMeta
  Lean.withExporting (isExporting := (← Command.getScope).isPublic) do
  Command.liftTermElabM do
    -- Whether we may access private `name`s here depends on whether it is a theorem, so first
    -- resolve in private scope always (also open alias namespace prefix, matching `def`)
    let name ← resolveAliasTarget alias.getId nameStx
    let cinfo ← withoutExporting <| getConstInfo name
    let declMods ← elabModifiers mods
    Lean.withExporting (isExporting := declMods.isInferredPublic (← getEnv)) do
    unless wasOriginallyTheorem (← getEnv) name do
      -- Now check again in correct scope for defs
      discard <| resolveAliasTarget alias.getId nameStx
    let (attrs, machineApplicable) := setDeprecatedTarget name declMods.attrs
    let env ← getEnv
    let declMods := { declMods with
      computeKind :=
        if isNoncomputable env name || scopeNoncomputable then .noncomputable
        else if isMarkedMeta env name || scopeMeta then .meta
        else declMods.computeKind
      isUnsafe := declMods.isUnsafe || cinfo.isUnsafe
      attrs
    }
    let (declName, _) ← mkDeclName (← getCurrNamespace) declMods alias.getId
    let decl : Declaration := if wasOriginallyTheorem (← getEnv) name then
      .thmDecl { cinfo.toConstantVal with
        name := declName
        value := mkConst name (cinfo.toConstantVal.levelParams.map mkLevelParam)
      }
    else
      .defnDecl { cinfo.toConstantVal with
        name := declName
        value := mkConst name (cinfo.levelParams.map mkLevelParam)
        hints := .regular 0 -- FIXME
        safety := if declMods.isUnsafe then .unsafe else .safe
      }
    checkNotAlreadyDeclared declName
    addDecl decl
    if declMods.isNoncomputable then
      modifyEnv (addNoncomputable · declName)
    else
      if declMods.isMeta then
        modifyEnv (markMeta · declName)
      compileDecl decl
    addDeclarationRangesFromSyntax declName (← getRef) alias
    Term.addTermInfo' alias (← mkConstWithLevelParams declName) (isBinder := true)
    if let some doc := declMods.docString? then
      addDocString declName (mkNullNode #[]) doc
    enableRealizationsForConst declName
    let info := AliasInfo.plain name
    setAliasInfo info declName
    Term.applyAttributes declName declMods.attrs
    if machineApplicable then
      modifyEnv (machineApplicableDeprecated.tag · declName)
    addAliasDocstring declName info

/--
Given a possibly forall-quantified iff expression `prf`, produce a value for one
of the implication directions (determined by `mp`).
-/
def mkIffMpApp (mp : Bool) (ty prf : Expr) : MetaM Expr := do
  Meta.forallTelescope ty fun xs ty => do
    let some (lhs, rhs) := ty.iff?
      | throwError "Target theorem must have the form `∀ x y z, a ↔ b`"
    Meta.mkLambdaFVars xs <|
      mkApp3 (mkConst (if mp then ``Iff.mp else ``Iff.mpr)) lhs rhs (mkAppN prf xs)

private def addSide (mp : Bool) (declName : Name) (declMods : Modifiers) (thm : ConstantInfo) :
    TermElabM Unit := do
  checkNotAlreadyDeclared declName
  let value ← mkIffMpApp mp thm.type (mkConst thm.name (thm.levelParams.map mkLevelParam))
  let type ← Meta.inferType value
  addDecl <| Declaration.thmDecl {
    name := declName
    value := value
    type := type
    levelParams := thm.levelParams
  }
  if let some doc := declMods.docString? then
    addDocString declName (mkNullNode #[]) doc
  let info := if mp then AliasInfo.forward thm.name else AliasInfo.reverse thm.name
  setAliasInfo info declName
  Term.applyAttributes declName declMods.attrs
  addAliasDocstring declName info

@[inherit_doc «alias»]
elab (name := aliasLR) mods:declModifiers "alias "
    "⟨" aliasFwd:binderIdent ", " aliasRev:binderIdent "⟩" " := " name:ident : command => do
  Lean.withExporting (isExporting := (← Command.getScope).isPublic) do
  Command.liftTermElabM do
    -- The target of an iff alias is always a theorem, so resolve in non-exporting mode to
    -- support private theorem targets even when the aliases themselves are public.
    let name ← withoutExporting <| realizeGlobalConstNoOverloadWithInfo name
    let thm ← withoutExporting <| getConstInfo name
    let declMods ← elabModifiers mods
    let declMods := { declMods with attrs := (setDeprecatedTarget name declMods.attrs).1 }
    -- Now enter scope where we want to put the new decls
    Lean.withExporting (isExporting := declMods.isInferredPublic (← getEnv)) do
    if let `(binderIdent| $idFwd:ident) := aliasFwd then
      let (declName, _) ← mkDeclName (← getCurrNamespace) declMods idFwd.getId
      addSide true declName declMods thm
      addDeclarationRangesFromSyntax declName (← getRef) idFwd
      Term.addTermInfo' idFwd (← mkConstWithLevelParams declName) (isBinder := true)
    if let `(binderIdent| $idRev:ident) := aliasRev then
      let (declName, _) ← mkDeclName (← getCurrNamespace) declMods idRev.getId
      addSide false declName declMods thm
      addDeclarationRangesFromSyntax declName (← getRef) idRev
      Term.addTermInfo' idRev (← mkConstWithLevelParams declName) (isBinder := true)

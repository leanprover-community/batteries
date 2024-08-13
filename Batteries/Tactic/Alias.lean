/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, David Renshaw, François G. Dorais
-/
import Lean.Elab.Command
import Lean.Elab.DeclarationRange
import Lean.Compiler.NoncomputableAttr
import Lean.DocString
import Batteries.CodeAction.Deprecated

/-!
# The `alias` command

The `alias` command is used to create synonyms. The plain command can create a synonym of any
declaration. There is also a version to create synonyms for the forward and reverse implications of
an iff theorem.
-/

namespace Batteries.Tactic.Alias

open Lean Elab Parser.Command Std

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


/-- Environment extension for registering aliases -/
initialize aliasExt : SimpleScopedEnvExtension (Name × AliasInfo) (NameMap AliasInfo) ←
  registerSimpleScopedEnvExtension {
    addEntry := fun st (n, i) => st.insert n i
    initial := {}
  }

/-- Get the alias information for a name -/
def getAliasInfo [Monad m] [MonadEnv m] (name : Name) : m (Option AliasInfo) := do
  return aliasExt.getState (← getEnv) |>.find? name

/-- Set the alias info for a new declaration -/
def setAliasInfo [MonadEnv m] (info : AliasInfo) (declName : Name) : m Unit :=
  modifyEnv (aliasExt.addEntry · (declName, info))

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

/--
  The command `alias name := target` creates a synonym of `target` with the given name.

  The command `alias ⟨fwd, rev⟩ := target` creates synonyms for the forward and reverse directions
  of an iff theorem. Use `_` if only one direction is required.

  These commands accept all modifiers and attributes that `def` and `theorem` do.
 -/
elab (name := alias) mods:declModifiers "alias " alias:ident " := " name:ident : command =>
  Command.liftTermElabM do
    let name ← realizeGlobalConstNoOverloadWithInfo name
    let cinfo ← getConstInfo name
    let declMods ← elabModifiers mods
    let (attrs, machineApplicable) := setDeprecatedTarget name declMods.attrs
    let declMods := { declMods with
      isNoncomputable := declMods.isNoncomputable || isNoncomputable (← getEnv) name
      isUnsafe := declMods.isUnsafe || cinfo.isUnsafe
      attrs
    }
    let (declName, _) ← mkDeclName (← getCurrNamespace) declMods alias.getId
    let decl : Declaration := if let .thmInfo t := cinfo then
      .thmDecl { t with
        name := declName
        value := mkConst name (t.levelParams.map mkLevelParam)
      }
    else
      .defnDecl { cinfo.toConstantVal with
        name := declName
        value := mkConst name (cinfo.levelParams.map mkLevelParam)
        hints := .regular 0 -- FIXME
        safety := if declMods.isUnsafe then .unsafe else .safe
      }
    checkNotAlreadyDeclared declName
    if declMods.isNoncomputable then
      addDecl decl
    else
      addAndCompile decl
    Lean.addDeclarationRanges declName {
      range := ← getDeclarationRange (← getRef)
      selectionRange := ← getDeclarationRange alias
    }
    Term.addTermInfo' alias (← mkConstWithLevelParams declName) (isBinder := true)
    addDocString' declName declMods.docString?
    Term.applyAttributes declName declMods.attrs
    let info := (← getAliasInfo name).getD <| AliasInfo.plain name
    setAliasInfo info declName
    if machineApplicable then
      modifyEnv (machineApplicableDeprecated.tag · declName)
    /- alias doesn't trigger the missing docs linter so we add a default. We can't just check
      `declMods` because a docstring may have been added by an attribute. -/
    if (← findDocString? (← getEnv) declName).isNone then
      let mut doc := info.toString
      if let some origDoc ← findDocString? (← getEnv) name then
        doc := s!"{doc}\n\n---\n\n{origDoc}"
      addDocString declName doc

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

private def addSide (mp : Bool) (declName : Name) (declMods : Modifiers) (thm : TheoremVal) :
    TermElabM Unit := do
  checkNotAlreadyDeclared declName
  let value ← mkIffMpApp mp thm.type thm.value
  let type ← Meta.inferType value
  addDecl <| Declaration.thmDecl { thm with
    name := declName
    value := value
    type := type
  }
  addDocString' declName declMods.docString?
  Term.applyAttributes declName declMods.attrs
  let info := match ← getAliasInfo thm.name with
    | some (.plain name) => if mp then AliasInfo.forward name else AliasInfo.reverse name
    | _ => if mp then AliasInfo.forward thm.name else AliasInfo.reverse thm.name
  setAliasInfo info declName
  /- alias doesn't trigger the missing docs linter so we add a default. We can't just check
    `declMods` because a docstring may have been added by an attribute. -/
  if (← findDocString? (← getEnv) declName).isNone then
    let mut doc := info.toString
    if let some origDoc ← findDocString? (← getEnv) thm.name then
      doc := s!"{doc}\n\n---\n\n{origDoc}"
    addDocString declName doc

@[inherit_doc «alias»]
elab (name := aliasLR) mods:declModifiers "alias "
    "⟨" aliasFwd:binderIdent ", " aliasRev:binderIdent "⟩" " := " name:ident : command =>
  Command.liftTermElabM do
    let name ← realizeGlobalConstNoOverloadWithInfo name
    let declMods ← elabModifiers mods
    let declMods := { declMods with attrs := (setDeprecatedTarget name declMods.attrs).1 }
    let .thmInfo thm ← getConstInfo name | throwError "Target must be a theorem"
    if let `(binderIdent| $idFwd:ident) := aliasFwd then
      let (declName, _) ← mkDeclName (← getCurrNamespace) declMods idFwd.getId
      addSide true declName declMods thm
      Lean.addDeclarationRanges declName {
        range := ← getDeclarationRange (← getRef)
        selectionRange := ← getDeclarationRange idFwd
      }
      Term.addTermInfo' idFwd (← mkConstWithLevelParams declName) (isBinder := true)
    if let `(binderIdent| $idRev:ident) := aliasRev then
      let (declName, _) ← mkDeclName (← getCurrNamespace) declMods idRev.getId
      addSide false declName declMods thm
      Lean.addDeclarationRanges declName {
        range := ← getDeclarationRange (← getRef)
        selectionRange := ← getDeclarationRange idRev
      }
      Term.addTermInfo' idRev (← mkConstWithLevelParams declName) (isBinder := true)

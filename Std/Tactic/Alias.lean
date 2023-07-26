/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, David Renshaw, François G. Dorais
-/
import Lean.Elab.Command
import Lean.Elab.DeclarationRange
import Lean.Compiler.NoncomputableAttr

/-!
# The `alias` command

TODO
-/

namespace Std.Tactic.Alias

open Lean Elab Parser.Command

/--
  The command `alias name := target` creates a synonym of `target` with the given name.

  The command `alias ⟨fwd, rev⟩ := target` creates synonyms for the forward and reverse directions
  of an iff theorem. Use `_` if only one direction is required.

  These commands accept all modifiers and attributes that `def` and `theorem` do.
 -/
elab (name := alias) mods:declModifiers "alias " alias:ident " := " name:ident : command =>
  Command.liftTermElabM do
    let resolved ← resolveGlobalConstNoOverloadWithInfo name
    let const ← getConstInfo resolved
    let declMods ← elabModifiers mods
    let (declName, _) ← mkDeclName (← getCurrNamespace) declMods alias.getId
    let decl : Declaration := match const with
      | Lean.ConstantInfo.thmInfo t =>
        .thmDecl { t with
          name := declName
          value := mkConst resolved (t.levelParams.map mkLevelParam)
        }
      | Lean.ConstantInfo.defnInfo c
      | Lean.ConstantInfo.quotInfo c
      | Lean.ConstantInfo.inductInfo c -- Also alias constructors and recursors?
      | Lean.ConstantInfo.axiomInfo c
      | Lean.ConstantInfo.opaqueInfo c
      | Lean.ConstantInfo.ctorInfo c
      | Lean.ConstantInfo.recInfo c =>
        .defnDecl { c with
          name := declName
          value := mkConst resolved (c.levelParams.map mkLevelParam)
          hints := .regular 0 -- FIXME
          safety := if declMods.isUnsafe then .unsafe else .safe
        }
    checkNotAlreadyDeclared declName
    if declMods.isNoncomputable then
      addDecl decl
    else
      addAndCompile decl
    addDocString' declName declMods.docString?
    Term.applyAttributes declName declMods.attrs
    /- alias doesn't trigger the missing docs linter so we add a default -/
    if (← findDocString? (← getEnv) declName).isNone then
      addDocString declName s!"**Alias** of {const.name}"

/--
Given a possibly forall-quantified iff expression `prf`, produce a value for one
of the implication directions (determined by `mp`).
-/
def mkIffMpApp (mp : Bool) (ty prf : Expr) : MetaM Expr := do
  Meta.forallTelescope ty fun xs ty ↦ do
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
  /- alias doesn't trigger the missing docs linter so we add a default -/
  if (← findDocString? (← getEnv) declName).isNone then
    if mp then
      addDocString declName s!"**Alias** for the forward direction of {thm.name}"
    else
      addDocString declName s!"**Alias** for the reverse direction of {thm.name}"

@[inherit_doc «alias»]
elab (name := aliasLR) mods:declModifiers "alias "
    "⟨" aliasFwd:binderIdent ", " aliasRev:binderIdent "⟩" " := " name:ident : command =>
  Command.liftTermElabM do
    let resolved ← resolveGlobalConstNoOverloadWithInfo name
    let declMods ← elabModifiers mods
    match ← getConstInfo resolved with
    | .thmInfo thm =>
      if let `(binderIdent| $x:ident) := aliasFwd then
        addSide true x.getId declMods thm
      if let `(binderIdent| $x:ident) := aliasRev then
        addSide false x.getId declMods thm
    | _ => throwError "Target must be a theorem"

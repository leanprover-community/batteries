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

open Lean Elab Parser.Command Term

/-- Like `++`, except that if the right argument starts with `_root_` the namespace will be
ignored.
```
addNamespaceUnlessRoot `a.b `c.d = `a.b.c.d
addNamespaceUnlessRoot `a.b `_root_.c.d = `c.d
```

TODO: Move this declaration to a more central location.
-/
@[inline] def addNamespaceUnlessRoot (ns : Name) (n : Name) : Name :=
  if rootNamespace.isPrefixOf n then removeRoot n else ns ++ n

/-- An alias can be in one of three forms -/
inductive Target where
  /-- Plain alias -/
  | plain : Name → Target
  /-- Forward direction of an iff alias -/
  | forward : Name → Target
  /-- Reverse direction of an iff alias -/
  | reverse : Name → Target

/-- The name underlying an alias target -/
def Target.name : Target → Name
  | Target.plain n => n
  | Target.forward n => n
  | Target.reverse n => n

#check Lean.Elab.Modifiers

/-- The docstring for an alias. -/
def Target.toString : Target → String
  | Target.plain n => s!"**Alias** of `{n}`."
  | Target.forward n => s!"**Alias** of the forward direction of `{n}`."
  | Target.reverse n => s!"**Alias** of the reverse direction of `{n}`."

/-- New alias, simple case -/
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
    applyAttributes declName declMods.attrs
    if (← findDocString? (← getEnv) declName).isNone then
      match declMods.docString? with
      | some s => addDocString declName s
      | none => addDocString declName s!"**Alias** of {resolved}"

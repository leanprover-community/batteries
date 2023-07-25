/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, David Renshaw
-/
import Lean.Elab.Command
import Lean.Elab.DeclarationRange
import Lean.Compiler.NoncomputableAttr

/-!
# The `alias` command

This file defines an `alias` command, which can be used to create copies
of a theorem or definition with different names.

Syntax:

```lean
/-- doc string -/
alias my_theorem ← alias1 alias2 ...
```

This produces defs or theorems of the form:

```lean
/-- doc string -/
theorem alias1 : <type of my_theorem> := my_theorem

/-- doc string -/
theorem alias2 : <type of my_theorem> := my_theorem
```

Iff alias syntax:

```lean
alias A_iff_B ↔ B_of_A A_of_B
alias A_iff_B ↔ ..
```

This gets an existing biconditional theorem `A_iff_B` and produces
the one-way implications `B_of_A` and `A_of_B` (with no change in
implicit arguments). A blank `_` can be used to avoid generating one direction.
The `..` notation attempts to generate the 'of'-names automatically when the
input theorem has the form `A_iff_B` or `A_iff_B_left` etc.
-/

namespace Std.Tactic.Alias

open Lean Elab Parser.Command

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

/-- The docstring for an alias. -/
def Target.toString : Target → String
  | Target.plain n => s!"**Alias** of `{n}`."
  | Target.forward n => s!"**Alias** of the forward direction of `{n}`."
  | Target.reverse n => s!"**Alias** of the reverse direction of `{n}`."

/--
The `alias` command can be used to create copies
of a theorem or definition with different names.

Syntax:

```lean
/-- doc string -/
alias my_theorem ← alias1 alias2 ...
```

This produces defs or theorems of the form:

```lean
/-- doc string -/
theorem alias1 : <type of my_theorem> := my_theorem

/-- doc string -/
theorem alias2 : <type of my_theorem> := my_theorem
```

Iff alias syntax:

```lean
alias A_iff_B ↔ B_of_A A_of_B
alias A_iff_B ↔ ..
```

This gets an existing biconditional theorem `A_iff_B` and produces
the one-way implications `B_of_A` and `A_of_B` (with no change in
implicit arguments). A blank `_` can be used to avoid generating one direction.
The `..` notation attempts to generate the 'of'-names automatically when the
input theorem has the form `A_iff_B` or `A_iff_B_left` etc.

The `protected` modifier can be used to add protected aliases.
-/
elab (name := alias) doc:(docComment)?
    protect:("protected ")? "alias " name:ident " ←" aliases:(ppSpace ident)* : command => do
  let visibility : Visibility := if protect.isSome then .protected else .regular
  let resolved ← resolveGlobalConstNoOverloadWithInfo name
  let const ← getConstInfo resolved
  let ns ← getCurrNamespace
  for a in aliases do withRef a do
    let declName ← applyVisibility visibility <| addNamespaceUnlessRoot ns a.getId
    let decl ← match const with
    | Lean.ConstantInfo.defnInfo d =>
      pure <| .defnDecl { d with
        name := declName
        value := mkConst resolved (d.levelParams.map mkLevelParam)
      }
    | Lean.ConstantInfo.thmInfo t =>
      pure <| .thmDecl { t with
        name := declName
        value := mkConst resolved (t.levelParams.map mkLevelParam)
      }
    | _ => throwError "alias only works with def or theorem"
    checkNotAlreadyDeclared declName
    addDeclarationRanges declName {
      range := ← getDeclarationRange (← getRef)
      selectionRange := ← getDeclarationRange a
    }
    -- TODO add @alias attribute
    Command.liftTermElabM do
      if isNoncomputable (← getEnv) resolved then
        addDecl decl
        setEnv <| addNoncomputable (← getEnv) declName
      else
        addAndCompile decl
      Term.addTermInfo' a (← mkConstWithLevelParams declName) (isBinder := true)
      let target := Target.plain resolved
      let docString := match doc with
        | none => target.toString
        | some d => d.getDocString
      addDocString declName docString

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

/-- Given a constant representing an iff decl, adds a decl for one of the implication directions. -/
def aliasIff (doc : Option (TSyntax `Lean.Parser.Command.docComment)) (ci : ConstantInfo)
    (ref : Syntax) (name : Name) (isForward : Bool) : TermElabM Unit := do
  let value ← mkIffMpApp isForward ci.type ci.value!
  let type ← Meta.inferType value
  -- TODO add @alias attribute
  addDeclarationRanges name {
    range := ← getDeclarationRange (← getRef)
    selectionRange := ← getDeclarationRange ref
  }
  addDecl <| .thmDecl { name, value, type, levelParams := ci.levelParams }
  Term.addTermInfo' ref (← mkConstWithLevelParams name) (isBinder := true)
  let target := if isForward then Target.forward ci.name else Target.reverse ci.name
  let docString := match doc with
    | none => target.toString
    | some d => d.getDocString
  addDocString name docString

@[inherit_doc «alias»]
elab (name := aliasLR) doc:(docComment)?
    protect:("protected ")? "alias " name:ident " ↔ " left:binderIdent ppSpace right:binderIdent : command => do
  let visibility : Visibility := if protect.isSome then .protected else .regular
  let resolved ← resolveGlobalConstNoOverloadWithInfo name
  let const ← getConstInfo resolved
  let ns ← getCurrNamespace
  Command.liftTermElabM do
    if let `(binderIdent| $x:ident) := left then
      let declName ← applyVisibility visibility <| addNamespaceUnlessRoot ns x.getId
      aliasIff doc const x declName (isForward := true)
    if let `(binderIdent| $x:ident) := right then
      let declName ← applyVisibility visibility <| addNamespaceUnlessRoot ns x.getId
      aliasIff doc const x declName (isForward := false)

@[inherit_doc «alias»]
elab (name := aliasLRDots) doc:(docComment)? protect:("protected ")? "alias " name:ident " ↔ " tk:".." : command => do
  let visibility : Visibility := if protect.isSome then .protected else .regular
  let resolved ← resolveGlobalConstNoOverloadWithInfo name
  let const ← getConstInfo resolved
  let (parent, base) ← match resolved with
    | .str n s => pure (n, s)
    | _ => throwError "alias only works for string names"
  let components := base.splitOn "_iff_"
  if components.length != 2 then throwError "LHS must be of the form *_iff_*"
  let forward := String.intercalate "_of_" components.reverse
  let backward := String.intercalate "_of_" components
  Command.liftTermElabM do
    let declName ← applyVisibility visibility (.str parent forward)
    aliasIff doc const tk declName (isForward := true)
    let declName ← applyVisibility visibility (.str parent backward)
    aliasIff doc const tk declName (isForward := false)

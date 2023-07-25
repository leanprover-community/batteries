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

/-- New alias, simple case -/
elab (name := alias) mods:declModifiers "alias " alias:ident " := " name:ident : command => do
  let resolved ← resolveGlobalConstNoOverloadWithInfo name
  let const ← getConstInfo resolved
  let tgt := Target.plain resolved
  let ns ← getCurrNamespace
  let declMods ← elabModifiers mods
  let declMods := if declMods.docString?.isSome then declMods else
      {declMods with docString? := some <| tgt.toString}
  let (declName, _) ← mkDeclName ns declMods alias.getId
  let decl : Declaration := match const with
    | Lean.ConstantInfo.thmInfo t =>
      .thmDecl { t with
        name := declName
        value := mkConst resolved (t.levelParams.map mkLevelParam)
      }
    | Lean.ConstantInfo.defnInfo d =>
      .defnDecl { d with
        name := declName
        value := mkConst resolved (d.levelParams.map mkLevelParam)
      }
    | Lean.ConstantInfo.quotInfo q =>
      .defnDecl { q with
        name := declName
        value := mkConst resolved (q.levelParams.map mkLevelParam)
        hints := .regular 0 -- Check?
        safety := .safe
      }
    | Lean.ConstantInfo.axiomInfo c
    | Lean.ConstantInfo.opaqueInfo c
    | Lean.ConstantInfo.inductInfo c
    | Lean.ConstantInfo.ctorInfo c
    | Lean.ConstantInfo.recInfo c =>
      .defnDecl { c with
        name := declName
        value := mkConst resolved (c.levelParams.map mkLevelParam)
        hints := .regular 0 -- Check?
        safety := if c.isUnsafe then .unsafe else .safe
      }
  checkNotAlreadyDeclared declName
  Command.liftTermElabM <| addDecl decl

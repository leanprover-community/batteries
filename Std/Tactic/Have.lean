/-
Copyright (c) 2022 Arthur Paulino. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Paulino, Edward Ayers, Mario Carneiro
-/
import Lean

/-!
# Extending `have`, `let` and `suffices`

This file extends the `have`, `let`, and `suffices` tactics to allow the addition of hypotheses to
the context without requiring their proofs to be provided immediately.
-/

namespace Std.Tactic

open Lean Elab.Tactic Meta Parser Term Syntax.MonadTraverser

/-- A parser for optional binder identifiers -/
def optBinderIdent : Parser := leading_parser
  -- Note: the withResetCache is because leading_parser seems to add a cache boundary,
  -- which causes the `hygieneInfo` parser not to be able to undo the trailing whitespace
  (ppSpace >> Term.binderIdent) <|> withResetCache hygieneInfo

/-- Retrieves the name of the optional identifier, if provided. Returns `this` otherwise. -/
def optBinderIdent.get (id : TSyntax ``optBinderIdent) : Name :=
  if id.raw[0].isIdent then id.raw[0].getId else HygieneInfo.mkIdent ⟨id.raw[0]⟩ `this |>.getId

/--
Uses `checkColGt` to prevent

```lean
have h
exact Nat
```

From being interpreted as
```lean
have h
  exact Nat
```
-/
def haveIdLhs : Parser :=
  optBinderIdent >> many (ppSpace >>
    checkColGt "expected to be indented" >> letIdBinder) >> optType

/--
Use `have` to create a new hypothesis,
but create a new goal for the value rather than providing it after `:=`.
-/
syntax "have" haveIdLhs : tactic
/--
Use `let` to create a new hypothesis,
but create a new goal for the value rather than providing it after `:=`.
-/
syntax "let " haveIdLhs : tactic
/--
Use `suffices` to create a new hypothesis,
but create a new goal for the value rather than providing it after `:=`.
-/
syntax "suffices" haveIdLhs : tactic

open Elab Term in
/--
Adds hypotheses to the context, turning them into goals to be proved later.

If the bound term is intended to be kept in the context, pass `keepTerm : Bool := true`.
This allows extending the `let` tactic.

Returns the new goal corresponding to the new hypothesis,
and the original goal with this hypothesis.
-/
def haveLater (goal : MVarId)
    (name : TSyntax ``optBinderIdent) (bis : Array (TSyntax ``letIdBinder))
    (ty : Option Term := none) (keepTerm : Bool := false) : TermElabM (MVarId × MVarId) :=
  goal.withContext do
    let n := optBinderIdent.get name
    let (new, ty, pf) ← elabBinders bis fun es => do
      let ty ← match ty with
      | none => mkFreshTypeMVar
      | some stx => withRef stx do
          let e ← Term.elabTerm stx none
          Term.synthesizeSyntheticMVars false
          instantiateMVars e
      let pf ← mkFreshExprMVar ty MetavarKind.syntheticOpaque n
      pure (pf.mvarId!, ← mkForallFVars es ty, ← mkLambdaFVars es pf)
    let declFn := if keepTerm then MVarId.define else MVarId.assert
    let (fvar, orig) ← (← declFn goal n ty pf).intro1P
    orig.withContext do
      Term.addTermInfo' (isBinder := true) name.raw[0] (mkFVar fvar)
    pure (new, orig)

/-- An extension of the `have` tactic that turns the hypothesis into a goal to be proved later. -/
elab_rules : tactic
| `(tactic| have $n:optBinderIdent $bs* $[: $ty:term]?) => do
  let (new, orig) ← haveLater (← getMainGoal) n bs ty
  replaceMainGoal [new, orig]

/--
An extension of the `suffices` tactic that turns the hypothesis into a goal to be proved later.
-/
elab_rules : tactic
| `(tactic| suffices $n:optBinderIdent $bs* $[: $ty:term]?) => do
  let (new, orig) ← haveLater (← getMainGoal) n bs ty
  replaceMainGoal [orig, new]

/-- An extension of the `let` tactic that turns the hypothesis into a goal to be proved later. -/
elab_rules : tactic
| `(tactic| let $n:optBinderIdent $bs* $[: $ty:term]?) => do
  let (new, orig) ← haveLater (← getMainGoal) n bs ty (keepTerm := true)
  replaceMainGoal [new, orig]

end Std.Tactic

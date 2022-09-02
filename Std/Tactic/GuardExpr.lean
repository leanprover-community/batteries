/-
Copyright (c) 2021 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Lean.Elab.Tactic.ElabTerm
import Lean.Elab.Tactic.Basic
import Lean.Meta.Basic

namespace Std.Tactic.GuardExpr
open Lean Elab Tactic

/--
The various `guard_*` tactics have similar matching specifiers for how equal expressions
have to be to pass the tactic.
This inductive gives the different specifiers that can be selected.
-/
inductive MatchKind
| /-- A syntactic match means that the `Expr`s are `==` after stripping `MData` -/
  syntactic
| /-- A defeq match `isDefEqGuarded` returns true. (Note that unification is allowed here.) -/
  defEq
| /-- An alpha-eq match means that `Expr.eqv` returns true. -/
  alphaEq

/-- Syntactic matching for `guard_hyp` types -/
syntax colonS := " : "
/-- Alpha-eq matching for `guard_hyp` types -/
syntax colonA := " :ₐ "
/-- The `guard_hyp` type specifier, either `:` or `:ₐ` -/
syntax colon := colonS <|> colonA

/-- Syntactic matching for `guard_hyp` values -/
syntax colonEqS := " := "
/-- Alpha-eq matching for `guard_hyp` values -/
syntax colonEqA := " :=ₐ "
/-- The `guard_hyp` value specifier, either `:=` or `:=ₐ` -/
syntax colonEq := colonEqS <|> colonEqA

/-- Syntactic matching for `guard_expr` -/
syntax equalS := " == "
/-- Def-eq matching for `guard_expr` -/
syntax equalD := " = "
/-- Alpha-eq matching for `guard_expr` -/
syntax equalA := " =ₐ "
/-- The `guard_expr` matching specifier, either `==`, `=`, or `=ₐ` -/
syntax equal := equalS <|> equalD <|> equalA

/-- Converts a `colon` syntax into a `MatchKind` -/
def colon.toMatchKind : TSyntax ``colon → Option MatchKind
  | `(colon| :) => some .syntactic
  | `(colon| :ₐ) => some .alphaEq
  | _ => none

/-- Converts a `colonEq` syntax into a `MatchKind` -/
def colonEq.toMatchKind : TSyntax ``colonEq → Option MatchKind
  | `(colonEq| :=) => some .syntactic
  | `(colonEq| :=ₐ) => some .alphaEq
  | _ => none

/-- Converts a `equal` syntax into a `MatchKind` -/
def equal.toMatchKind : TSyntax ``equal → Option MatchKind
  | `(equal| =) => some .defEq
  | `(equal| ==) => some .syntactic
  | `(equal| =ₐ) => some .alphaEq
  | _ => none

/-- Applies the selected matching rule to two expressions. -/
def MatchKind.isEq (a b : Expr) : MatchKind → MetaM Bool
  | .syntactic => return a.consumeMData == b.consumeMData
  | .alphaEq => return a.eqv b
  | .defEq => withoutModifyingState <| Lean.Meta.isDefEqGuarded a b

/--
Check equality of two expressions.
* `guard_expr e == e'` checks that `e` and `e'` are syntactically equal.
* `guard_expr e =ₐ e'` checks that `e` and `e'` are alpha-equivalent.
* `guard_expr e = e'` checks that `e` and `e'` are definitionally equal.
-/
elab (name := guardExprStrict) "guard_expr " r:term:51 eq:equal p:term : tactic =>
  withMainContext do
    let r ← elabTerm r none
    let p ← elabTerm p none
    let some mk := equal.toMatchKind eq | throwUnsupportedSyntax
    if ← mk.isEq r p then throwError "failed: {r} != {p}"

/--
Check the target agrees with a given expression.
* `guard_target == e` checks that the target is syntactically equal to `e`.
* `guard_target =ₐ e` checks that the target is alpha-equivalent to `e`.
* `guard_target = e` checks that the target is definitionally equal to `e`.
-/
elab (name := guardTargetStrict) "guard_target" eq:equal r:term : tactic =>
  withMainContext do
    let r ← elabTerm r none
    let t ← getMainTarget
    let some mk := equal.toMatchKind eq | throwUnsupportedSyntax
    if ← mk.isEq r t then throwError "target of main goal is {t}, not {r}"

/--
Check that a named hypothesis has a given type and/or value.

* `guardHyp h : t` checks the type up to syntactic equality,
* `guardHyp h :ₐ t` checks the type up to alpha equality.
* `guardHyp h := v` checks value up to syntactic equality,
* `guardHyp h :=ₐ v` checks the value up to alpha equality.
-/
syntax (name := guardHyp) "guard_hyp " term:max (colon term)? (colonEq term)? : tactic

@[inheritDoc guardHyp, tactic guardHyp] def evalGuardHyp : Lean.Elab.Tactic.Tactic := fun
  | `(tactic| guard_hyp $h $[$c $ty]? $[$eq $val]?) =>
    withMainContext do
      let fvarid ← getFVarId h
      let lDecl ←
        match (← getLCtx).find? fvarid with
        | none => throwError m!"hypothesis {h} not found"
        | some lDecl => pure lDecl
      if let (some c, some p) := (c, ty) then
        let some mk := colon.toMatchKind c | throwUnsupportedSyntax
        let e ← elabTerm p none
        let hty ← instantiateMVars lDecl.type
        if ← mk.isEq e hty then throwError m!"hypothesis {h} has type {hty}"
      match lDecl.value?, val with
      | none, some _        => throwError m!"{h} is not a let binding"
      | some _, none        => throwError m!"{h} is a let binding"
      | some hval, some val =>
        let some mk := eq.bind colonEq.toMatchKind | throwUnsupportedSyntax
        let e ← elabTerm val none
        let hval ← instantiateMVars hval
        if ← mk.isEq e hval then throwError m!"hypothesis {h} has value {hval}"
      | none, none          => pure ()
  | _ => throwUnsupportedSyntax

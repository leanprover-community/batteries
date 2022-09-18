/-
Copyright (c) 2021 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Lean.Elab.Tactic.Conv.Basic
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
syntax (name := guardExpr) "guard_expr " term:51 equal term : tactic
@[inheritDoc guardExpr] syntax (name := guardExprConv) "guard_expr " term:51 equal term : conv

@[inheritDoc guardExpr, tactic guardExpr, tactic guardExprConv]
def evalGuardExpr : Tactic := fun
  | `(tactic| guard_expr $r $eq:equal $p)
  | `(conv| guard_expr $r $eq:equal $p) => withMainContext do
    let r ← elabTerm r none
    let p ← elabTerm p none
    let some mk := equal.toMatchKind eq | throwUnsupportedSyntax
    unless ← mk.isEq r p do throwError "failed: {r} != {p}"
  | _ => throwUnsupportedSyntax

/--
Check the target agrees with a given expression.
* `guard_target == e` checks that the target is syntactically equal to `e`.
* `guard_target =ₐ e` checks that the target is alpha-equivalent to `e`.
* `guard_target = e` checks that the target is definitionally equal to `e`.
-/
syntax (name := guardTarget) "guard_target " equal term : tactic
@[inheritDoc guardTarget] syntax (name := guardTargetConv) "guard_target " equal term : conv

@[inheritDoc guardTarget, tactic guardTarget, tactic guardTargetConv]
def evalGuardTarget : Tactic :=
  let go eq r getTgt := withMainContext do
    let r ← elabTerm r none
    let t ← getTgt
    let some mk := equal.toMatchKind eq | throwUnsupportedSyntax
    unless ← mk.isEq r t do throwError "target of main goal is {t}, not {r}"
  fun
  | `(tactic| guard_target $eq $r) => go eq r getMainTarget
  | `(conv| guard_target $eq $r) => go eq r Conv.getLhs
  | _ => throwUnsupportedSyntax

/--
Check that a named hypothesis has a given type and/or value.

* `guard_hyp h : t` checks the type up to syntactic equality,
* `guard_hyp h :ₐ t` checks the type up to alpha equality.
* `guard_hyp h := v` checks value up to syntactic equality,
* `guard_hyp h :=ₐ v` checks the value up to alpha equality.
-/
syntax (name := guardHyp)
  "guard_hyp " term:max (colon term)? (colonEq term)? : tactic
@[inheritDoc guardHyp] syntax (name := guardHypConv)
  "guard_hyp " term:max (colon term)? (colonEq term)? : conv

@[inheritDoc guardHyp, tactic guardHyp, tactic guardHypConv]
def evalGuardHyp : Tactic := fun
  | `(tactic| guard_hyp $h $[$c $ty]? $[$eq $val]?)
  | `(conv| guard_hyp $h $[$c $ty]? $[$eq $val]?) => withMainContext do
    if c.isNone && eq.isNone then throwUnsupportedSyntax
    let fvarid ← getFVarId h
    let lDecl ←
      match (← getLCtx).find? fvarid with
      | none => throwError m!"hypothesis {h} not found"
      | some lDecl => pure lDecl
    if let (some c, some p) := (c, ty) then
      let some mk := colon.toMatchKind c | throwUnsupportedSyntax
      let e ← elabTerm p none
      let hty ← instantiateMVars lDecl.type
      unless ← mk.isEq e hty do throwError m!"hypothesis {h} has type {hty}, not {e}"
    match lDecl.value?, val with
    | none, some _        => throwError m!"{h} is not a let binding"
    | some _, none        => throwError m!"{h} is a let binding"
    | some hval, some val =>
      let some mk := eq.bind colonEq.toMatchKind | throwUnsupportedSyntax
      let e ← elabTerm val none
      let hval ← instantiateMVars hval
      unless ← mk.isEq e hval do throwError m!"hypothesis {h} has value {hval}, not {e}"
    | none, none          => pure ()
  | _ => throwUnsupportedSyntax

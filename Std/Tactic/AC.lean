/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dany Fabian
-/
import Std.Data.AC
import Std.Lean.Tactic
import Lean.Meta.Tactic.Refl
import Lean.Meta.Tactic.Simp.Main

namespace Std.Tactic.AC
open Lean Meta Elab Tactic
open Data AC

private structure PreContext where
  id : Nat
  op : Expr
  assoc : Expr
  comm : Option Expr
  idem : Option Expr
  deriving Inhabited

instance : ContextInformation (PreContext × Array Bool) where
  isComm ctx := ctx.1.comm.isSome
  isIdem ctx := ctx.1.idem.isSome
  isNeutral ctx x := ctx.2[x]!

instance : EvalInformation PreContext AC.Expr where
  arbitrary _ := Data.AC.Expr.var 0
  evalOp _ := Data.AC.Expr.op
  evalVar _ x := Data.AC.Expr.var x

private def getInstance (cls : Name) (exprs : Array Expr) : MetaM (Option Expr) := do
  try
    let app ← mkAppM cls exprs
    trace[Tactic.AC] "trying: {indentExpr app}"
    let inst ← synthInstance app
    trace[Tactic.AC] "got instance"
    return some inst
  catch
  | _ => return none

private def preContext (expr : Expr) : MetaM (Option PreContext) := do
  if let some assoc := ←getInstance ``Associative #[expr] then
    return some
      { assoc,
        op := expr
        id := 0
        comm := ←getInstance ``Commutative #[expr]
        idem := ←getInstance ``IdempotentOp #[expr] }

  return none

private inductive PreExpr
  | op (lhs rhs : PreExpr)
  | var (e : Expr)

@[match_pattern] private def bin (op l r : Expr) :=
  Expr.app (Expr.app op l) r

private def toACExpr (op l r : Expr) : MetaM (Array Expr × AC.Expr) := do
  let (preExpr, vars) ←
    toPreExpr (mkApp2 op l r)
    |>.run HashSet.empty
  let vars := vars.toArray.insertionSort Expr.lt
  let varMap := vars.foldl (fun xs x => xs.insert x xs.size) HashMap.empty |>.find!

  return (vars, go varMap preExpr)
  where
    toPreExpr : Expr → StateT ExprSet MetaM PreExpr
    | e@(bin op₂ l r) => do
      if ←isDefEq op op₂ then
        return PreExpr.op (←toPreExpr l) (←toPreExpr r)
      modify fun vars => vars.insert e
      return PreExpr.var e
    | e => do
      modify fun vars => vars.insert e
      return PreExpr.var e

    go (varMap : Expr → Nat) : PreExpr → AC.Expr
    | PreExpr.op l r => Data.AC.Expr.op (go varMap l) (go varMap r)
    | PreExpr.var x => Data.AC.Expr.var (varMap x)

private def buildNormProof (preContext : PreContext) (l r : Expr) :
    MetaM (Lean.Expr × Lean.Expr) := do
  let (vars, ACExpr) ← toACExpr preContext.op l r

  let α ← inferType vars[0]!
  let u ← getLevel α
  let (isNeutrals, context) ← mkContext α u vars
  let ACExprNormed := Data.AC.evalList AC.Expr preContext <|
    Data.AC.norm (preContext, isNeutrals) ACExpr
  let tgt := convertTarget vars ACExprNormed
  let lhs := convert ACExpr
  let rhs := convert ACExprNormed
  let proof := mkAppN (mkConst ``Context.eq_of_norm [u])
    #[α, context, lhs, rhs, ←mkEqRefl (mkConst ``Bool.true)]
  return (proof, tgt)
where
  mkContext (α : Expr) (u : Level) (vars : Array Expr) : MetaM (Array Bool × Expr) := do
    let arbitrary := vars[0]!
    let zero := mkLevelZeroEx ()
    let plift := mkApp (mkConst ``PLift [zero])
    let pliftUp := mkApp2 (mkConst ``PLift.up [zero])
    let noneE tp   := mkApp  (mkConst ``Option.none [zero]) (plift tp)
    let someE tp v := mkApp2 (mkConst ``Option.some [zero]) (plift tp) (pliftUp tp v)
    let vars ← vars.mapM fun x => do
      let isNeutral :=
        let isNeutralClass := mkApp3 (mkConst ``LawfulIdentity [u]) α preContext.op x
        match ←getInstance ``LawfulIdentity #[preContext.op, x] with
        | none => (false, noneE isNeutralClass)
        | some isNeutral => (true, someE isNeutralClass isNeutral)

      return (isNeutral.1, mkApp4 (mkConst ``Variable.mk [u]) α preContext.op x isNeutral.2)

    let (isNeutrals, vars) := vars.unzip
    let vars := vars.toList
    let vars ← mkListLit (mkApp2 (mkConst ``Variable [u]) α preContext.op) vars

    let comm :=
      let commClass := mkApp2 (mkConst ``Commutative [u]) α preContext.op
      match preContext.comm with
      | none => noneE commClass
      | some comm => someE commClass comm

    let idem :=
      let idemClass := mkApp2 (mkConst ``IdempotentOp [u]) α preContext.op
      match preContext.idem with
      | none => noneE idemClass
      | some idem => someE idemClass idem

    return (isNeutrals, mkApp7 (mkConst ``Std.Data.AC.Context.mk [u]) α preContext.op
      preContext.assoc comm idem vars arbitrary)

  convert : AC.Expr → Expr
    | .op l r => mkApp2 (mkConst ``Data.AC.Expr.op) (convert l) (convert r)
    | .var x => mkApp (mkConst ``Data.AC.Expr.var) $ mkNatLit x

  convertTarget (vars : Array Expr) : AC.Expr → Expr
    | .op l r => mkApp2 preContext.op (convertTarget vars l) (convertTarget vars r)
    | .var x => vars[x]!

private def rewriteUnnormalized (mvarId : MVarId) : MetaM Unit := do
  let simpCtx :=
    {
      simpTheorems  := {}
      congrTheorems := (← getSimpCongrTheorems)
      config        := Simp.neutralConfig
    }
  let tgt ← instantiateMVars (← mvarId.getType)
  let (res, _) ← Simp.main tgt simpCtx (methods := { post })
  let newGoal ← applySimpResultToTarget mvarId tgt res
  newGoal.refl
where
  post (e : Expr) : SimpM Simp.Step := do
    let ctx ← Simp.getContext
    match e, ctx.parent? with
    | bin op₁ l r, some (bin op₂ _ _) =>
      if ←isDefEq op₁ op₂ then
        return Simp.Step.done { expr := e }
      match ←preContext op₁ with
      | some pc =>
        let (proof, newTgt) ← buildNormProof pc l r
        return Simp.Step.done { expr := newTgt, proof? := proof }
      | none => return Simp.Step.done { expr := e }
    | bin op l r, _ =>
      match ←preContext op with
      | some pc =>
        let (proof, newTgt) ← buildNormProof pc l r
        return Simp.Step.done { expr := newTgt, proof? := proof }
      | none => return Simp.Step.done { expr := e }
    | e, _ => return Simp.Step.done { expr := e }

/--
`ac_rfl` proves equalities up to application of an associative and commutative operator.
```
instance : Associative (α := Nat) (.+.) := ⟨Nat.add_assoc⟩
instance : Commutative (α := Nat) (.+.) := ⟨Nat.add_comm⟩
example (a b c d : Nat) : a + b + c + d = d + (b + c) + a := by ac_rfl
```
-/
elab "ac_rfl" : tactic => do
  let goal ← getMainGoal
  goal.withContext <| rewriteUnnormalized goal

initialize registerTraceClass `Tactic.AC

end Std.Tactic.AC

/-
Copyright (c) 2022 Siddhartha Gadgil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Siddhartha Gadgil, Mario Carneiro
-/
import Lean.Elab.Tactic.ElabTerm
import Batteries.Tactic.Alias

/-!
# `trans` tactic

This implements the `trans` tactic, which can apply transitivity theorems with an optional middle
variable argument.
-/

/-- Compose using transitivity, homogeneous case. -/
def Trans.simple {r : α → α → Sort _} [Trans r r r] : r a b → r b c → r a c := trans

@[deprecated (since := "2024-10-18")]
alias Trans.heq := Trans.trans

namespace Batteries.Tactic
open Lean Meta Elab

initialize registerTraceClass `Tactic.trans

/-- Classification for a relation application identifying the positions of the two explicit
arguments. -/
structure RelKind where
  /-- The number of arguments after the relation expression (including implicits) -/
  size : Nat
  /-- The position of the first explicit argument, `ix < iz < size` -/
  ix : Nat
  /-- The position of the second explicit argument, `ix < iz < size` -/
  iz : Nat
  deriving Inhabited, BEq

/-- Constructs a relation application using kind `k`. -/
def RelKind.mkRel (rel : Expr) (k : RelKind) (x z : Expr) :=
  mkAppOptM' rel <| Array.replicate k.size none |>.set! k.ix x |>.set! k.iz z

/-- Environment extension storing transitivity lemmas -/
initialize transExt :
    SimpleScopedEnvExtension (Name × Array DiscrTree.Key) (DiscrTree Name) ←
  registerSimpleScopedEnvExtension {
    addEntry := fun dt (n, ks) => dt.insertCore ks n
    initial := {}
  }

/-- solving `e ← mkAppM' f #[x]` -/
def getExplicitFuncArg? (e : Expr) : MetaM (Option <| Expr × Expr) := do
  match e with
  | Expr.app f a => do
    if ← isDefEq (← mkAppM' f #[a]) e then
      return some (f, a)
    else
      getExplicitFuncArg? f
  | _ => return none

/-- refining `tgt ← mkAppM' rel #[x, z]` dropping more arguments if possible -/
def getExplicitRelArg (tgt rel x z : Expr) (k : RelKind) : MetaM (Expr × RelKind) := do
  match rel with
  | Expr.app rel' _ => do
    let k' : RelKind := { size := k.size + 1, ix := k.ix + 1, iz := k.iz + 1 }
    let check ←
      try
        let folded ← k'.mkRel rel' x z
        isDefEq folded tgt
      catch _ =>
        pure false
    if !check then
      return (rel, k)
    else
      getExplicitRelArg tgt rel' x z k'
  | _ => return (rel, k)

/-- Internal definition for `trans` tactic. Either a binary relation or a non-dependent
arrow. -/
inductive TransRelation
  /-- Expression for transitive relation. -/
  | app (rel : Expr) (k : RelKind)
  /-- Constant name for transitive relation. -/
  | implies (name : Name) (bi : BinderInfo)

/-- Finds an explicit binary relation in the argument, if possible. -/
def getRel (tgt : Expr) : MetaM (Option (TransRelation × Expr × Expr)) :=
  match tgt with
  | .forallE name binderType body info => return .some (.implies name info, binderType, body)
  | _ => tgt.withApp fun f args => do
    let info := (← getFunInfo f).paramInfo
    let rec
      /-- returns the largest `i` less than the input s.t. `info[i]` is explicit -/
      findExplicit : Nat → Option Nat
      | 0 => none
      | i+1 => if info[i]!.binderInfo.isExplicit then some i else findExplicit i
    if args.size ≠ info.size then return none
    let some iz := findExplicit args.size | return none
    let some ix := findExplicit iz | return none
    let x := args[ix]!
    let z := args[iz]!
    let rel := mkAppRange f 0 ix args
    let k : RelKind := { size := args.size - ix, ix := 0, iz := iz - ix }
    let check ←
      try
        let folded ← k.mkRel rel x z
        isDefEq folded tgt
      catch _ => pure false
    if check then
      let (rel, k) ← getExplicitRelArg tgt rel x z k
      return some (.app rel k, x, z)
    else
      return none

initialize registerBuiltinAttribute {
  name := `trans
  descr := "transitive relation"
  add := fun decl _ kind => MetaM.run' do
    let declTy := (← getConstInfo decl).type
    withReducible <| forallTelescopeReducing declTy fun xs targetTy => do
      let fail := throwError
        "@[trans] attribute only applies to lemmas proving
        x ∼ y → y ∼ z → x ∼ z, got {indentExpr declTy} with target {indentExpr targetTy}"
      let some (.app rel _, _, _) ← getRel targetTy | fail
      let some yzHyp := xs.back? | fail
      let some xyHyp := xs.pop.back? | fail
      let some (.app _ _, _, _) ← getRel (← yzHyp.fvarId!.getType) | fail
      let some (.app _ _, _, _) ← getRel (← xyHyp.fvarId!.getType) | fail
      let key ← withReducible <| DiscrTree.mkPath rel
      transExt.add (decl, key) kind
}

open Lean.Elab.Tactic

/--
`trans` applies to a goal whose target has the form `t ~ u` where `~` is a transitive relation,
that is, a relation which has a transitivity lemma tagged with the attribute [trans].

* `trans s` replaces the goal with the two subgoals `t ~ s` and `s ~ u`.
* If `s` is omitted, then a metavariable is used instead.

Additionally, `trans` also applies to a goal whose target has the form `t → u`,
in which case it replaces the goal with `t → s` and `s → u`.
-/
elab "trans" t?:(ppSpace colGt term)? : tactic => withMainContext do
  let tgt := (← instantiateMVars (← (← getMainGoal).getType)).cleanupAnnotations
  let .some (rel, x, z) ← getRel tgt
    | throwError "transitivity lemmas only apply to binary relations and \
                  non-dependent arrows, not{indentExpr tgt}"
  match rel with
  | .implies name info =>
    -- only consider non-dependent arrows
    if z.hasLooseBVars then
      throwError "`trans` is not implemented for dependent arrows{indentExpr tgt}"
    -- parse the intermeditate term
    let middleType ← mkFreshExprMVar none
    let t'? ← t?.mapM (elabTermWithHoles · middleType (← getMainTag))
    let middle ← (t'?.map (pure ·.1)).getD (mkFreshExprMVar middleType)
    liftMetaTactic fun goal => do
      -- create two new goals
      let g₁ ← mkFreshExprMVar (some <| .forallE name x middle info) .synthetic
      let g₂ ← mkFreshExprMVar (some <| .forallE name middle z info) .synthetic
      -- close the original goal with `fun x => g₂ (g₁ x)`
      goal.assign (.lam name x (.app g₂ (.app g₁ (.bvar 0))) .default)
      pure <| [g₁.mvarId!, g₂.mvarId!] ++ if let some (_, gs') := t'? then gs' else [middle.mvarId!]
    return
  | .app rel k =>
    trace[Tactic.trans] "goal decomposed: rel = {rel}, x = {x}, z = {z}"
    -- first trying the homogeneous case
    try
      let ty ← inferType x
      let t'? ← t?.mapM (elabTermWithHoles · ty (← getMainTag))
      let s ← saveState
      trace[Tactic.trans] "trying homogeneous case"
      let lemmas :=
        (← (transExt.getState (← getEnv)).getUnify rel).push ``Trans.simple
      for lem in lemmas do
        trace[Tactic.trans] "trying lemma {lem}"
        try
          liftMetaTactic fun g => do
            let lemTy ← inferType (← mkConstWithLevelParams lem)
            let arity ← withReducible <| forallTelescopeReducing lemTy fun es _ => pure es.size
            trace[Tactic.trans] "arity: {arity}"
            trace[Tactic.trans] "lemma-type: {lemTy}"
            let y ← (t'?.map (pure ·.1)).getD (mkFreshExprMVar ty)
            trace[Tactic.trans] "obtained y = {y}"
            trace[Tactic.trans] "rel = {rel}, x = {x}, z = {z}"
            let g₁ ← mkFreshExprMVar (some <| ← k.mkRel rel x y) .synthetic
            let g₂ ← mkFreshExprMVar (some <| ← k.mkRel rel y z) .synthetic
            g.assign (← mkAppOptM lem (.replicate (arity - 2) none ++ #[some g₁, some g₂]))
            pure <| [g₁.mvarId!, g₂.mvarId!] ++
              if let some (_, gs') := t'? then gs' else [y.mvarId!]
          return
        catch _ => s.restore
      pure ()
    catch _ =>
      trace[Tactic.trans] "trying heterogeneous case"
      let t'? ← t?.mapM (elabTermWithHoles · none (← getMainTag))
      let s ← saveState
      for lem in (← (transExt.getState (← getEnv)).getUnify rel).push
          ``HEq.trans |>.push ``Trans.trans do
        try
          liftMetaTactic fun g => do
            trace[Tactic.trans] "trying lemma {lem}"
            let lemTy ← inferType (← mkConstWithLevelParams lem)
            let arity ← withReducible <| forallTelescopeReducing lemTy fun es _ => pure es.size
            trace[Tactic.trans] "arity: {arity}"
            trace[Tactic.trans] "lemma-type: {lemTy}"
            let y ← (t'?.map (pure ·.1)).getD (mkFreshExprMVar none)
            trace[Tactic.trans] "obtained y = {y}"
            trace[Tactic.trans] "rel = {rel}, x = {x}, z = {z}"
            let g₂ ← mkFreshExprMVar (some <| ← k.mkRel rel y z) .synthetic
            let g₁ ← mkFreshExprMVar (some <| ← k.mkRel rel x y) .synthetic
            g.assign (← mkAppOptM lem (.replicate (arity - 2) none ++ #[some g₁, some g₂]))
            pure <| [g₁.mvarId!, g₂.mvarId!] ++
              if let some (_, gs') := t'? then gs' else [y.mvarId!]
          return
        catch e =>
          trace[Tactic.trans] "failed: {e.toMessageData}"
          s.restore
      throwError "no applicable transitivity lemma found for {indentExpr tgt}"

/-- Synonym for `trans` tactic. -/
macro "transitivity" e:(ppSpace colGt term)? : tactic => `(tactic| trans $(e)?)

end Batteries.Tactic

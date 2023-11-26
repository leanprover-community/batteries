/-
Copyright (c) 2023 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
import Lean.Meta.Tactic.Replace
import Lean.Elab.Tactic.Location

/-!
# Implementation of the `change at h` tactic
-/

namespace Lean.MVarId

open Lean Elab Meta

/-- Function to help do the revert/intro pattern, running some code inside a context
where certain variables have been reverted before re-introing them.
It will push `FVarId` alias information into info trees for you according to a simple protocol.

- `fvarIds` is an array of `fvarIds` to revert. These are passed to
  `Lean.MVarId.revert` with `preserveOrder := true`, hence the function
  raises an error if they cannot be reverted in the provided order.
- `k` is given the goal with all the variables reverted and
  the array of reverted `FVarId`s, with the requested `FVarId`s at the beginning.
  It must return a tuple of a value, an array describing which `FVarIds` to link,
  and a mutated `MVarId`.

The `a : Array (Option FVarId)` array returned by `k` is interpreted in the following way.
The function will intro `a.size` variables, and then for each non-`none` entry we
create an FVar alias between it and the corresponding `intro`ed variable.
For example, having `k` return `fvars.map .some` causes all reverted variables to be
`intro`ed and linked.

Returns the value returned by `k` along with the resulting goal.
 -/
def withReverted (mvarId : MVarId) (fvarIds : Array FVarId)
    (k : MVarId → Array FVarId → MetaM (α × Array (Option FVarId) × MVarId))
    (clearAuxDeclsInsteadOfRevert := false) : MetaM (α × MVarId) := do
  let (xs, mvarId) ← mvarId.revert fvarIds true clearAuxDeclsInsteadOfRevert
  let (r, xs', mvarId) ← k mvarId xs
  let (ys, mvarId) ← mvarId.introNP xs'.size
  mvarId.withContext do
    for x? in xs', y in ys do
      if let some x := x? then
        pushInfoLeaf (.ofFVarAliasInfo { id := y, baseId := x, userName := ← y.getUserName })
  return (r, mvarId)

/--
Replace the type of the free variable `fvarId` with `typeNew`.

If `checkDefEq = true` then throws an error if `typeNew` is not definitionally
equal to the type of `fvarId`. Otherwise this function assumes `typeNew` and the type
of `fvarId` are definitionally equal.

This function is the same as `Lean.MVarId.changeLocalDecl` but makes sure to push substitution
information into the infotree.
-/
def changeLocalDecl' (mvarId : MVarId) (fvarId : FVarId) (typeNew : Expr)
    (checkDefEq := true) : MetaM MVarId := do
  mvarId.checkNotAssigned `changeLocalDecl
  let (_, mvarId) ← mvarId.withReverted #[fvarId] fun mvarId fvars => mvarId.withContext do
    let check (typeOld : Expr) : MetaM Unit := do
      if checkDefEq then
        unless ← isDefEq typeNew typeOld do
          throwTacticEx `changeLocalDecl mvarId
            m!"given type{indentExpr typeNew}\nis not definitionally equal to{indentExpr typeOld}"
    let finalize (targetNew : Expr) := do
      return ((), fvars.map .some, ← mvarId.replaceTargetDefEq targetNew)
    match ← mvarId.getType with
    | .forallE n d b bi => do check d; finalize (.forallE n typeNew b bi)
    | .letE n t v b ndep => do check t; finalize (.letE n typeNew v b ndep)
    | _ => throwTacticEx `changeLocalDecl mvarId "unexpected auxiliary target"
  return mvarId

end Lean.MVarId

open Lean Elab Tactic Meta

/-- `change` can be used to replace the main goal or its local
variables with definitionally equal ones.

For example, if `n : ℕ` and the current goal is `⊢ n + 2 = 2`, then
```lean
change _ + 1 = _
```
changes the goal to `⊢ n + 1 + 1 = 2`. The tactic also applies to the local context.
If `h : n + 2 = 2` and `h' : n + 3 = 4` are in the local context, then
```lean
change _ + 1 = _ at h h'
```
changes their types to be `h : n + 1 + 1 = 2` and `h' : n + 2 + 1 = 4`.

Change is like `refine` in that every placeholder needs to be solved for by unification,
but you can use named placeholders and `?_` where you want `change` to create new goals.

The tactic `show e` is interchangeable with `change e`, where the pattern `e` is applied to
the main goal. -/
elab_rules : tactic
  | `(tactic| change $newType:term $[$loc:location]?) => do
    withLocation (expandOptLocation (Lean.mkOptionalNode loc))
      (atLocal := fun h => do
        let hTy ← h.getType
        -- This is a hack to get the new type to elaborate in the same sort of way that
        -- it would for a `show` expression for the goal.
        let mvar ← mkFreshExprMVar none
        let (_, mvars) ← elabTermWithHoles
                          (← `(term | show $newType from $(← Term.exprToSyntax mvar))) hTy `change
        liftMetaTactic fun mvarId => do
          return (← mvarId.changeLocalDecl' h (← inferType mvar)) :: mvars)
      (atTarget := evalTactic <| ← `(tactic| refine_lift show $newType from ?_))
      (failed := fun _ => throwError "change tactic failed")

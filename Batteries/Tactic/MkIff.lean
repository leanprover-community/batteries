/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, David Renshaw
-/
module

public meta import Lean.Elab.DeclarationRange
public meta import Lean.Meta.Tactic.Cases
public meta import Batteries.Lean.Meta.Basic
public meta import Batteries.Lean.Name
public meta import Lean.Meta.Tactic.Apply
public meta import Lean.Meta.Tactic.Constructor
public meta import Lean.Elab.Command

/-!
# mk_iff_of_inductive_prop

This file defines a command `mk_iff_of_inductive_prop` that generates `iff` rules for
inductive `Prop`s. For example, when applied to `List.IsChain`, it creates a declaration with
the following type:

```lean
∀ {α : Type*} (R : α → α → Prop) (l : List α),
  List.IsChain R l ↔ l = [] ∨ (∃ a, l = [a]) ∨
    ∃ a b l', R a b ∧ List.IsChain R (b :: l') ∧ l = a :: b :: l'
```

This tactic can be called using either the `mk_iff_of_inductive_prop` user command or
the `mk_iff` attribute.
-/

meta section

namespace Lean

/-- Make an n-ary `Or` application. `mkOrN []` returns `False`.
This mirrors the core `Lean.mkAndN`. -/
public def mkOrN : List Expr → Expr
  | []      => mkConst ``False
  | [p]     => p
  | p :: ps => mkOr p (mkOrN ps)

namespace Meta

/--
Takes an array `xs` of free variables and a body term `e`, and builds the
existential `∃ x₁ ⋯ xₙ, e`, abstracting each `xᵢ` from `e` and from the types
of the later binders.

This is the existential analogue of `Lean.Meta.mkForallFVars`. Unlike `∀`/`λ`,
`Exists` is not a primitive binder (`∃ x, p` is `Exists fun x => p`), so this is
built by folding `Exists` applications over `mkLambdaFVars`. Whenever a binder
has a `Prop`-valued type and does not occur in the remaining body, the
non-dependent `∃ _ : p, q` is emitted as `p ∧ q` instead.
-/
public def mkExistsFVars (xs : Array Expr) (e : Expr) : MetaM Expr :=
  xs.foldrM (fun x b => do
    let t ← inferType x
    let l := (← inferType t).sortLevel!
    if x.occurs b || l != .zero then
      -- `∃ x, b`; rebuild the lambda with a default binder so `x` prints explicitly
      let .lam n d body _ ← mkLambdaFVars #[x] b
        | panic! "mkLambdaFVars did not produce a lambda"
      pure (mkApp2 (.const ``Exists [l]) t (.lam n d body .default))
    else
      pure (mkAnd t b))
    e

/-- `select m n` runs `right` `m` times; if `m < n`, then it also runs `left` once.
Fails if `n < m`. -/
def select (m n : Nat) (goal : MVarId) : MetaM MVarId :=
  match m,n with
  | 0, 0             => pure goal
  | 0, (_ + 1)       => do
    let [newGoal] ← goal.nthConstructor `left 0 (some 2)
      | throwError "expected only one new goal"
    pure newGoal
  | (m + 1), (n + 1) => do
    let [newGoal] ← goal.nthConstructor `right 1 (some 2)
      | throwError "expected only one new goal"
    select m n newGoal
  | _, _             => failure

/-- `compactRelation bs as_ps`: Produce a relation of the form:
```lean
R := fun as => ∃ bs, ⋀_i a_i = p_i[bs]
```
This relation is user-visible, so we compact it by removing each `b_j` where a `p_i = b_j`, and
hence `a_i = b_j`. We need to take care when there are `p_i` and `p_j` with `p_i = p_j = b_k`.
-/
partial def compactRelation :
    List Expr → List (Expr × Expr) → List (Option Expr) × List (Expr × Expr) × (Expr → Expr)
| [],    asPs => ([], asPs, id)
| b::bs, asPs =>
  match asPs.span (fun ⟨_, p⟩ => p != b) with
    | (_, []) => -- found nothing in ps equal to b
      let (bs, asPs', subst) := compactRelation bs asPs
      (b::bs, asPs', subst)
    | (ps₁, (a, _) :: ps₂) => -- found one that matches b. Remove it.
      let i := fun e => e.replaceFVar b a
      let (bs, asPs', subst) :=
        compactRelation (bs.map i) ((ps₁ ++ ps₂).map (fun ⟨a, p⟩ => (a, i p)))
      (none :: bs, asPs', i ∘ subst)

/-- Auxiliary data associated with a single constructor of an inductive declaration.
-/
structure Shape : Type where
  /-- For each forall-bound variable in the type of the constructor, minus
  the "params" that apply to the entire inductive type, this list contains `true`
  if that variable has been kept after `compactRelation`.

  For example, `ReflTransGen.refl` has type
  ```lean
    ∀ {α : Type u_1} {r : α → α → Prop} {a : α}, ReflTransGen r a a
  ```
  where `α`, `r` and `a` are all "params", leaving no further variables, so
  `variablesKept = []`.

  `ReflTransGen.tail` has type
  ```lean
    ∀ {α : Type u_1} {r : α → α → Prop} {a : α} {b c : α},
       ReflTransGen r a b → r b c → ReflTransGen r a c
  ```
  where `α`, `r` and `a` are "params". The index `c` gets eliminated in a
  `compactRelation`, so `variablesKept = [true, false, true, true]`.
  -/
  variablesKept : List Bool

  /-- The number of equalities, or `none` in the case when we've reduced something
  of the form `p ∧ True` to just `p`.
  -/
  neqs : Option Nat

/-- Converts an inductive constructor `c` into a `Shape` that will be used later in
while proving the iff theorem, and a proposition representing the constructor.
-/
def constrToProp (univs : List Level) (params : List Expr) (idxs : List Expr) (c : Name) :
    MetaM (Shape × Expr) := do
  let type := (← getConstInfo c).instantiateTypeLevelParams univs
  let type' ← Meta.forallBoundedTelescope type (params.length) fun fvars ty => do
    pure <| ty.replaceFVars fvars params.toArray
  Meta.forallTelescope type' fun fvars ty => do
    let idxsInst := ty.getAppArgs.toList.drop params.length
    let (bs, eqs, subst) := compactRelation fvars.toList (idxs.zip idxsInst)
    let eqs ← eqs.mapM (fun ⟨idx, inst⟩ => do
      let ty ← idx.fvarId!.getType
      let instTy ← inferType inst
      let u := (← inferType ty).sortLevel!
      if ← isDefEq ty instTy
      then pure (mkApp3 (.const ``Eq [u]) ty idx inst)
      else pure (mkApp4 (.const ``HEq [u]) ty idx instTy inst))
    let (n, r) ← match bs.filterMap id, eqs with
    | [], [] => do
      pure (some 0, (mkConst ``True))
    | bs', [] => do
      let t : Expr ← bs'.getLast!.fvarId!.getType
      let l := (← inferType t).sortLevel!
      if l == Level.zero then do
        let r ← mkExistsFVars bs'.dropLast.toArray t
        pure (none, subst r)
      else do
        let r ← mkExistsFVars bs'.toArray (mkConst ``True)
        pure (some 0, subst r)
    | bs', _ => do
      let r ← mkExistsFVars bs'.toArray (Lean.mkAndN eqs)
      pure (some eqs.length, subst r)
    pure (⟨bs.map Option.isSome, n⟩, r)

/-- Splits the goal `n` times via the anonymous constructor (`And.intro`), and then applies
`constructor` to close each resulting subgoal.
-/
def splitThenConstructor (mvar : MVarId) (n : Nat) : MetaM Unit := do
  match n with
  | 0     =>
    let [] ← mvar.constructor | throwError "expected no subgoals"
    pure ()
  | n + 1 =>
    let [sg1, sg2] ← mvar.constructor | throwError "expected two subgoals"
    let [] ← sg1.constructor | throwError "expected no subgoals"
    splitThenConstructor sg2 n

/-- Proves the left to right direction of a generated iff theorem.
`shape` is the output of a call to `constrToProp`.
-/
def toCases (mvar : MVarId) (shape : List Shape) : MetaM Unit := do
  let ⟨h, mvar'⟩ ← mvar.intro1
  let subgoals ← mvar'.cases h
  let _ ← (shape.zip subgoals.toList).zipIdx.mapM fun ⟨⟨⟨shape, t⟩, subgoal⟩, p⟩ => do
    let vars := subgoal.fields
    let si := (shape.zip vars.toList).filterMap (fun ⟨c,v⟩ => if c then some v else none)
    let mvar'' ← select p (subgoals.size - 1) subgoal.mvarId
    match t with
    | none => do
      let v := vars[shape.length - 1]!
      -- provide a witness for every existential except the last, then close it with `v`
      let mv ← si.dropLast.foldlM (·.existsIntro ·) mvar''
      mv.assign v
    | some n => do
      let mv ← si.foldlM (·.existsIntro ·) mvar''
      splitThenConstructor mv (n - 1)
  pure ()

/-- Calls `cases` on `h` (assumed to be a binary sum) `n` times, and returns
the resulting subgoals and their corresponding new hypotheses.
-/
def nCasesSum (n : Nat) (mvar : MVarId) (h : FVarId) : MetaM (List (FVarId × MVarId)) :=
match n with
| 0 => pure [(h, mvar)]
| n' + 1 => do
  let #[sg1, sg2] ← mvar.cases h | throwError "expected two case subgoals"
  let #[Expr.fvar fvar1] ← pure sg1.fields | throwError "expected fvar"
  let #[Expr.fvar fvar2] ← pure sg2.fields | throwError "expected fvar"
  let rest ← nCasesSum n' sg2.mvarId fvar2
  pure ((fvar1, sg1.mvarId)::rest)

/-- Calls `cases` on `h` (assumed to be a binary product) `n` times, and returns
the resulting subgoal and the new hypotheses.
-/
def nCasesProd (n : Nat) (mvar : MVarId) (h : FVarId) : MetaM (MVarId × List FVarId) :=
match n with
| 0 => pure (mvar, [h])
| n' + 1 => do
  let #[sg] ← mvar.cases h | throwError "expected one case subgoals"
  let #[Expr.fvar fvar1, Expr.fvar fvar2] ← pure sg.fields | throwError "expected fvar"
  let (mvar', rest) ← nCasesProd n' sg.mvarId fvar2
  pure (mvar', fvar1::rest)

/--
Iterate over two lists, if the first element of the first list is `false`, insert `none` into the
result and continue with the tail of first list. Otherwise, wrap the first element of the second
list with `some` and continue with the tails of both lists. Return when either list is empty.

Example:
```
listBoolMerge [false, true, false, true] [0, 1, 2, 3, 4] = [none, (some 0), none, (some 1)]
```
-/
def listBoolMerge {α : Type u} : List Bool → List α → List (Option α)
  | [], _ => []
  | false :: xs, ys => none :: listBoolMerge xs ys
  | true :: xs, y :: ys => some y :: listBoolMerge xs ys
  | true :: _, [] => []

/-- Proves the right to left direction of a generated iff theorem.
-/
def toInductive (mvar : MVarId) (cs : List Name)
    (gs : List Expr) (s : List Shape) (h : FVarId) :
    MetaM Unit := do
  match s.length with
  | 0       => do let _ ← mvar.cases h
                  pure ()
  | (n + 1) => do
      let subgoals ← nCasesSum n mvar h
      let _ ← (cs.zip (subgoals.zip s)).mapM fun ⟨constrName, ⟨h, mv⟩, bs, e⟩ => do
        let n := (bs.filter id).length
        let (mvar', _fvars) ← match e with
        | none => nCasesProd (n-1) mv h
        | some 0 => do let ⟨mvar', fvars⟩ ← nCasesProd n mv h
                          let mvar'' ← mvar'.tryClear fvars.getLast!
                          pure ⟨mvar'', fvars⟩
        | some (e + 1) => do
           let (mv', fvars) ← nCasesProd n mv h
           let lastFv := fvars.getLast!
           let (mv2, fvars') ← nCasesProd e mv' lastFv

           /- `fvars'.foldlM subst mv2` fails when we have dependent equalities (`HEq`).
           `subst` will change the dependent hypotheses, so that the `uniq` local names
           are wrong afterwards. Instead we revert them and pull them out one-by-one. -/
           let (_, mv3) ← mv2.revert fvars'.toArray
           let mv4 ← fvars'.foldlM (fun mv _ => do let ⟨fv, mv'⟩ ← mv.intro1; subst mv' fv) mv3
           pure (mv4, fvars)
        mvar'.withContext do
          let fvarIds := (← getLCtx).getFVarIds.toList
          let gs := fvarIds.take gs.length
          let hs := (fvarIds.reverse.take n).reverse
          let m := gs.map some ++ listBoolMerge bs hs
          let args ← m.mapM fun a =>
            match a with
            | some v => pure (mkFVar v)
            | none => mkFreshExprMVar none
          let c ← mkConstWithFreshMVarLevels constrName
          let e := mkAppN c args.toArray
          let t ← inferType e
          let mt ← mvar'.getType
          let _ ← isDefEq t mt -- infer values for those mvars we just made
          mvar'.assign e


public section

/-- Implementation for both `mk_iff` and `mk_iff_of_inductive_prop`.
-/
def mkIffOfInductivePropImpl (ind : Name) (rel : Name) (relStx : Syntax) :
    MetaM Unit := do
  let .inductInfo inductVal ← getConstInfo ind |
    throwError "mk_iff only applies to inductive declarations"
  let constrs := inductVal.ctors
  let params := inductVal.numParams
  let type := inductVal.type

  let univNames := inductVal.levelParams
  let univs := univNames.map mkLevelParam
  let (thmTy, shape) ← Meta.forallTelescope type fun fvars ty => do
    if !ty.isProp then throwError "mk_iff only applies to prop-valued declarations"
    let lhs := mkAppN (mkConst ind univs) fvars
    let fvars' := fvars.toList
    let shapeRhss ← constrs.mapM (constrToProp univs (fvars'.take params) (fvars'.drop params))
    let (shape, rhss) := shapeRhss.unzip
    pure (← mkForallFVars fvars (mkIff lhs (Lean.mkOrN rhss)), shape)

  let mvar ← mkFreshExprMVar (some thmTy)
  let mvarId := mvar.mvarId!
  let (fvars, mvarId') ← mvarId.intros
  let [mp, mpr] ← mvarId'.apply (mkConst ``Iff.intro) | throwError "failed to split goal"

  toCases mp shape

  let ⟨mprFvar, mpr'⟩ ← mpr.intro1
  toInductive mpr' constrs ((fvars.toList.take params).map .fvar) shape mprFvar

  addDecl <| .thmDecl {
    name := rel
    levelParams := univNames
    type := thmTy
    value := ← instantiateMVars mvar
  }
  Elab.addDeclarationRangesFromSyntax rel (← getRef) relStx
  Elab.Term.addTermInfo' relStx (← mkConstWithLevelParams rel) (isBinder := true) |>.run'


/--
Applying the `mk_iff` attribute to an inductively-defined proposition `mk_iff` makes an `iff` rule
`r` with the shape `∀ ps is, i as ↔ ⋁_j, ∃ cs, is = cs`, where
* `ps` are the type parameters,
* `is` are the indices,
* `j` ranges over all possible constructors,
* the `cs` are the parameters for each of the constructors, and
* the equalities `is = cs` are the instantiations for each constructor for each of
  the indices to the inductive type `i`.

In each case, we remove constructor parameters (i.e. `cs`) when the corresponding equality would
be just `c = i` for some index `i`.

For example, if we try the following:
```lean
@[mk_iff]
structure Foo (m n : Nat) : Prop where
  equal : m = n
  sum_eq_two : m + n = 2
```

Then `#check foo_iff` returns:
```lean
foo_iff : ∀ (m n : Nat), Foo m n ↔ m = n ∧ m + n = 2
```

You can add an optional string after `mk_iff` to change the name of the generated lemma.
For example, if we try the following:
```lean
@[mk_iff bar]
structure Foo (m n : Nat) : Prop where
  equal : m = n
  sum_eq_two : m + n = 2
```

Then `#check bar` returns:
```lean
bar : ∀ (m n : ℕ), Foo m n ↔ m = n ∧ m + n = 2
```

See also the user command `mk_iff_of_inductive_prop`.
-/
syntax (name := mkIff) "mk_iff" (ppSpace ident)? : attr

/--
`mk_iff_of_inductive_prop i r` makes an `iff` rule for the inductively-defined proposition `i`.
The new rule `r` has the shape `∀ ps is, i as ↔ ⋁_j, ∃ cs, is = cs`, where
* `ps` are the type parameters,
* `is` are the indices,
* `j` ranges over all possible constructors,
* the `cs` are the parameters for each of the constructors, and
* the equalities `is = cs` are the instantiations for
  each constructor for each of the indices to the inductive type `i`.

In each case, we remove constructor parameters (i.e. `cs`) when the corresponding equality would
be just `c = i` for some index `i`.

For example, `mk_iff_of_inductive_prop` on `List.IsChain` produces:

```lean
∀ {α : Type*} (R : α → α → Prop) (l : List α),
  List.IsChain R l ↔ l = [] ∨ (∃ a, l = [a]) ∨
    ∃ a b l', R a b ∧ List.IsChain R (b :: l') ∧ l = a :: b :: l'
```

See also the `mk_iff` user attribute.
-/
syntax (name := mkIffOfInductiveProp) "mk_iff_of_inductive_prop " ident ppSpace ident : command

elab_rules : command
| `(command| mk_iff_of_inductive_prop $i:ident $r:ident) =>
    Elab.Command.liftCoreM <| MetaM.run' do
      mkIffOfInductivePropImpl i.getId r.getId r

initialize Lean.registerBuiltinAttribute {
  name := `mkIff
  descr := "Generate an `iff` lemma for an inductive `Prop`."
  add := fun decl stx _ => Lean.Meta.MetaM.run' do
    let (tgt, idStx) ← match stx with
      | `(attr| mk_iff $tgt:ident) =>
        pure ((← Elab.mkDeclName (← getCurrNamespace) {} tgt.getId).1, tgt.raw)
      | `(attr| mk_iff) => pure (decl.decapitalize.appendAfter "_iff", stx)
      | _ => throwError "unrecognized syntax"
    mkIffOfInductivePropImpl decl tgt idStx
}

end

end Meta

end Lean

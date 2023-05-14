/-
Copyright (c) 2021 Gabriel Ebner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner, Mario Carneiro
-/
import Std.Tactic.Basic
import Std.Tactic.RCases
import Std.Tactic.Ext.Attr

namespace Std.Tactic.Ext
open Lean Meta Elab Tactic


/--
Constructs the hypotheses for the extensionality lemma.
Calls the continuation `k` with the list of parameters to the structure,
two structure variables `x` and `y`, and a list of pairs `(field, ty)`
where `ty` is `x.field = y.field` or `HEq x.field y.field`.
-/
def withExtHyps (struct : Name)
    (k : Array Expr → (x y : Expr) → Array (Name × Expr) → MetaM α) : MetaM α := do
  unless isStructure (← getEnv) struct do throwError "not a structure: {struct}"
  let structC ← mkConstWithLevelParams struct
  forallTelescope (← inferType structC) fun params _ => do
  withNewBinderInfos (params.map (·.fvarId!, BinderInfo.implicit)) do
  withLocalDeclD `x (mkAppN structC params) fun x => do
  withLocalDeclD `y (mkAppN structC params) fun y => do
    let mut hyps := #[]
    for field in getStructureFieldsFlattened (← getEnv) struct (includeSubobjectFields := false) do
      let x_f ← mkProjection x field
      let y_f ← mkProjection y field
      if ← isProof x_f then
        pure ()
      else if ← isDefEq (← inferType x_f) (← inferType y_f) then
        hyps := hyps.push (field, ← mkEq x_f y_f)
      else
        hyps := hyps.push (field, ← mkHEq x_f y_f)
    k params x y hyps

/--
Creates the type of the extensionality lemma for the given structure,
elaborating to `x.1 = y.1 → x.2 = y.2 → x = y`, for example.
-/
scoped elab "ext_type%" struct:ident : term => do
  withExtHyps (← resolveGlobalConstNoOverloadWithInfo struct) fun params x y hyps => do
    let ty := hyps.foldr (init := ← mkEq x y) fun (f, h) ty =>
      mkForall f BinderInfo.default h ty
    mkForallFVars (params |>.push x |>.push y) ty

/-- Make an `Iff` application. -/
def mkIff (p q : Expr) : Expr := mkApp2 (mkConst ``Iff) p q

/-- Make an n-ary `And` application. `mkAndN []` returns `True`. -/
def mkAndN : List Expr → Expr
  | [] => mkConst ``True
  | [p] => p
  | p :: ps => mkAnd p (mkAndN ps)

/--
Creates the type of the iff-variant of the extensionality lemma for the given structure,
elaborating to `x = y ↔ x.1 = y.1 ∧ x.2 = y.2`, for example.
-/
scoped elab "ext_iff_type%" struct:ident : term => do
  withExtHyps (← resolveGlobalConstNoOverloadWithInfo struct) fun params x y hyps => do
    mkForallFVars (params |>.push x |>.push y) <|
      mkIff (← mkEq x y) <| mkAndN (hyps.map (·.2)).toList

macro_rules | `(declare_ext_theorems_for $struct:ident $[$prio]?) => do
  let names ← Macro.resolveGlobalName struct.getId.eraseMacroScopes
  let name ← match names.filter (·.2.isEmpty) with
    | [] => Macro.throwError s!"unknown constant {struct}"
    | [(name, _)] => pure name
    | _ => Macro.throwError s!"ambiguous name {struct}"
  let extName := mkIdentFrom struct (canonical := true) <| name.mkStr "ext"
  let extIffName := mkIdentFrom struct (canonical := true) <| name.mkStr "ext_iff"
  `(@[ext $[$prio]?] protected theorem $extName:ident : ext_type% $struct:ident :=
      fun {..} {..} => by intros; subst_eqs; rfl
    protected theorem $extIffName:ident : ext_iff_type% $struct:ident :=
      fun {..} {..} =>
        ⟨fun h => by cases h; split_ands <;> rfl,
         fun _ => by (repeat cases ‹_ ∧ _›); subst_eqs; rfl⟩)

/-- Apply a single extensionality lemma to `goal`. -/
def applyExtLemma (goal : MVarId) : MetaM (List MVarId) := goal.withContext do
  let tgt ← goal.getType'
  unless tgt.isAppOfArity ``Eq 3 do
    throwError "applyExtLemma only applies to equations, not{indentExpr tgt}"
  let ty := tgt.getArg! 0
  let s ← saveState
  for lem in ← getExtLemmas ty do
    try
      -- Note: We have to do this extra check to ensure that we don't apply e.g.
      -- funext to a goal `(?a₁ : ?b) = ?a₂` to produce `(?a₁ x : ?b') = ?a₂ x`,
      -- since this will loop.
      -- We require that the type of the equality is not changed by the `goal.apply c` line
      -- TODO: add flag to apply tactic to toggle unification vs. matching
      withNewMCtxDepth do
        let c ← mkConstWithFreshMVarLevels lem.declName
        let (_, _, declTy) ← withDefault <| forallMetaTelescopeReducing (← inferType c)
        guard (← isDefEq tgt declTy)
      return ← goal.apply (← mkConstWithFreshMVarLevels lem.declName)
    catch _ => s.restore
  throwError "no applicable extensionality lemma found for{indentExpr ty}"

/-- Apply a single extensionality lemma to the current goal. -/
elab "apply_ext_lemma" : tactic => liftMetaTactic applyExtLemma

/--
Postprocessor for `withExt` which runs `rintro` with the given patterns when the target is a
pi type.
-/
def tryIntros [Monad m] [MonadLiftT TermElabM m] (g : MVarId) (pats : List (TSyntax `rcasesPat))
    (k : MVarId → List (TSyntax `rcasesPat) → m Unit) : m Unit := do
  match pats with
  | [] => k (← (g.intros : TermElabM _)).2 []
  | p::ps =>
    if (← (g.withContext g.getType' : TermElabM _)).isForall then
      for g in ← RCases.rintro #[p] none g do
        k g ps
    else k g pats

/--
Applies a single extensionality lemma, using `pats` to introduce variables in the result.
Runs continuation `k` on each subgoal.
-/
def withExt1 [Monad m] [MonadLiftT TermElabM m] (g : MVarId) (pats : List (TSyntax `rcasesPat))
    (k : MVarId → List (TSyntax `rcasesPat) → m Unit) : m Unit := do
  for g in ← (applyExtLemma g : TermElabM _) do
    tryIntros g pats k

/--
Applies a extensionality lemmas recursively, using `pats` to introduce variables in the result.
Runs continuation `k` on each subgoal.
-/
def withExtN [Monad m] [MonadLiftT TermElabM m] [MonadExcept Exception m]
    (g : MVarId) (pats : List (TSyntax `rcasesPat))
    (k : MVarId → List (TSyntax `rcasesPat) → m Unit)
    (depth := 1000000) (failIfUnchanged := true) : m Unit :=
  match depth with
  | 0 => k g pats
  | depth+1 => do
    if failIfUnchanged then
      withExt1 g pats fun g pats => withExtN g pats k depth (failIfUnchanged := false)
    else try
      withExt1 g pats fun g pats => withExtN g pats k depth (failIfUnchanged := false)
    catch _ => k g pats

/--
Apply extensionality lemmas as much as possible, using `pats` to introduce the variables
in extensionality lemmas like `funext`. Returns a list of subgoals,
and the unconsumed patterns in each of those subgoals.
-/
def extCore (g : MVarId) (pats : List (TSyntax `rcasesPat))
    (depth := 1000000) (failIfUnchanged := true) :
    TermElabM (Array (MVarId × List (TSyntax `rcasesPat))) := do
  (·.2) <$> StateT.run (m := TermElabM) (s := #[])
    (withExtN g pats (fun g qs => modify (·.push (g, qs))) depth failIfUnchanged)

/--
* `ext pat*`: Apply extensionality lemmas as much as possible,
  using `pat*` to introduce the variables in extensionality lemmas like `funext`.
* `ext`: introduce anonymous variables whenever needed.
* `ext pat* : n`: apply ext lemmas only up to depth `n`.
-/
syntax "ext" (colGt ppSpace rintroPat)* (" : " num)? : tactic
elab_rules : tactic
  | `(tactic| ext $pats* $[: $n]?) => do
    let pats := RCases.expandRIntroPats pats
    let depth := n.map (·.getNat) |>.getD 1000000
    let gs ← extCore (← getMainGoal) pats.toList depth
    replaceMainGoal <| gs.map (·.1) |>.toList

/--
`ext1 pat*` is like `ext pat*` except it only applies one extensionality lemma instead
of recursing as much as possible.
-/
macro "ext1" xs:(colGt ppSpace rintroPat)* : tactic =>
  if xs.isEmpty then `(tactic| apply_ext_lemma <;> intros)
  else `(tactic| apply_ext_lemma <;> rintro $xs*)

-- TODO
/-- `ext1? pat*` is like `ext1 pat*` but gives a suggestion on what pattern to use -/
syntax "ext1?" (colGt ppSpace rintroPat)* : tactic
/-- `ext? pat*` is like `ext pat*` but gives a suggestion on what pattern to use -/
syntax "ext?" (colGt ppSpace rintroPat)* (" : " num)? : tactic

end Std.Tactic.Ext

attribute [ext] funext propext

@[ext] protected theorem PUnit.ext (x y : PUnit) : x = y := rfl
protected theorem Unit.ext (x y : Unit) : x = y := rfl

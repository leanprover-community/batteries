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

macro_rules | `(declare_ext_theorems_for $struct:ident) => do
  let extName := mkIdentFrom struct (canonical := true) <|
    struct.getId.eraseMacroScopes.mkStr "ext"
  let extIffName := mkIdentFrom struct (canonical := true) <|
    struct.getId.eraseMacroScopes.mkStr "ext_iff"
  `(@[ext] protected theorem $extName:ident : ext_type% $struct:ident :=
      fun {..} {..} => by intros; subst_eqs; rfl
    protected theorem $extIffName:ident : ext_iff_type% $struct:ident :=
      fun {..} {..} =>
        ⟨fun _ => by subst_eqs; split_ands <;> rfl,
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
      return ← goal.apply (← mkConstWithFreshMVarLevels lem)
    catch _ => s.restore
  throwError "no applicable extensionality lemma found for{indentExpr ty}"

/-- Apply a single extensionality lemma to the current goal. -/
elab "apply_ext_lemma" : tactic => liftMetaTactic applyExtLemma

/--
Runs continuation `k` in each subgoal produced by `ext pats`.
The continuation is passed the list of remaining patterns.
-/
def withExt [Monad m] [MonadLift TermElabM m] (g : MVarId) (pats : List (TSyntax `rcasesPat))
    (k : MVarId → List (TSyntax `rcasesPat) → m Unit) : m Unit := do
  for g in ← repeat' (m := MetaM) applyExtLemma [g] do
    match pats with
    | [] => k g []
    | p::ps =>
      for g in ← RCases.rintro mkNullNode #[p] none g do
        withExt g ps k

/--
Apply extensionality lemmas as much as possible, using `pats` to introduce the variables
in extensionality lemmas like `funext`.
-/
scoped elab "ext_or_skip" pats:(ppSpace rintroPat)* : tactic => do
  let pats ← RCases.expandRIntroPats pats
  let (_, gs) ← StateT.run (m := TermElabM) (s := #[]) <|
    withExt (← getMainGoal) pats.toList fun g _ => modify (·.push g)
  replaceMainGoal gs.toList

-- TODO: support `ext : n`

/--
* `ext pat*`: Apply extensionality lemmas as much as possible,
  using `pat*` to introduce the variables in extensionality lemmas like `funext`.
* `ext`: introduce anonymous variables whenever needed.
-/
syntax "ext" (colGt ppSpace rintroPat)* (" : " num)? : tactic
macro_rules
  | `(tactic| ext) => `(tactic| repeat (first | (intro) | apply_ext_lemma))
  | `(tactic| ext $xs*) => `(tactic| ext_or_skip $xs*)

/--
`ext1 pat*` is like `ext pat*` except it only applies one extensionality lemma instead
of recursing as much as possible.
-/
macro "ext1" xs:(colGt ppSpace rintroPat)* : tactic => `(tactic| (apply_ext_lemma; rintro $xs*))

-- TODO
/-- `ext1? pat*` is like `ext1 pat*` but gives a suggestion on what pattern to use -/
syntax "ext1?" (colGt ppSpace rintroPat)* : tactic
/-- `ext? pat*` is like `ext pat*` but gives a suggestion on what pattern to use -/
syntax "ext?" (colGt ppSpace rintroPat)* (" : " num)? : tactic

attribute [ext] funext propext

@[ext] protected theorem Unit.ext (x y : Unit) : x = y := rfl
@[ext] protected theorem PUnit.ext (x y : Unit) : x = y := rfl

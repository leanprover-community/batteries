/-
Copyright (c) 2021 Gabriel Ebner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner, Mario Carneiro
-/
import Std.Tactic.Basic
import Std.Tactic.RCases
import Std.Tactic.Ext.Attr
import Std.Tactic.TryThis

namespace Std.Tactic.Ext
open Lean Meta Elab Tactic Std.Tactic.TryThis

/-- Enables tracing in the `ext` tactic, displaying used extensionality lemmas.
Is set by `ext?` and `ext1?`. -/
register_option tactic.ext.trace : Bool := {
  defValue := false
  descr    := "When enabled, calls to `ext` will print a tactic sequence
  reproducing the `ext` call."
}

/-- Global variable tracking tactics used by `ext?`. This is a collection of
`apply $lem`, `rintro $pat`, `intros`, and `sorry` statements. -/
initialize usedExtTactics : IO.Ref (Array (Syntax.Tactic)) ← IO.mkRef #[]

/--
Constructs the hypotheses for the extensionality lemma.
Calls the continuation `k` with the list of parameters to the structure,
two structure variables `x` and `y`, and a list of pairs `(field, ty)`
where `ty` is `x.field = y.field` or `HEq x.field y.field`.
-/
def withExtHyps (struct : Name) (flat : Term)
    (k : Array Expr → (x y : Expr) → Array (Name × Expr) → MetaM α) : MetaM α := do
  let flat ← match flat with
  | `(true) => pure true
  | `(false) => pure false
  | _ => throwErrorAt flat "expected 'true' or 'false'"
  unless isStructure (← getEnv) struct do throwError "not a structure: {struct}"
  let structC ← mkConstWithLevelParams struct
  forallTelescope (← inferType structC) fun params _ => do
  withNewBinderInfos (params.map (·.fvarId!, BinderInfo.implicit)) do
  withLocalDeclD `x (mkAppN structC params) fun x => do
  withLocalDeclD `y (mkAppN structC params) fun y => do
    let mut hyps := #[]
    let fields := if flat then
      getStructureFieldsFlattened (← getEnv) struct (includeSubobjectFields := false)
    else
      getStructureFields (← getEnv) struct
    for field in fields do
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
scoped elab "ext_type%" flat:term:max struct:ident : term => do
  withExtHyps (← resolveGlobalConstNoOverloadWithInfo struct) flat fun params x y hyps => do
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
scoped elab "ext_iff_type%" flat:term:max struct:ident : term => do
  withExtHyps (← resolveGlobalConstNoOverloadWithInfo struct) flat fun params x y hyps => do
    mkForallFVars (params |>.push x |>.push y) <|
      mkIff (← mkEq x y) <| mkAndN (hyps.map (·.2)).toList

macro_rules | `(declare_ext_theorems_for $[(flat := $f)]? $struct:ident $(prio)?) => do
  let flat := f.getD (mkIdent `true)
  let names ← Macro.resolveGlobalName struct.getId.eraseMacroScopes
  let name ← match names.filter (·.2.isEmpty) with
    | [] => Macro.throwError s!"unknown constant {struct}"
    | [(name, _)] => pure name
    | _ => Macro.throwError s!"ambiguous name {struct}"
  let extName := mkIdentFrom struct (canonical := true) <| name.mkStr "ext"
  let extIffName := mkIdentFrom struct (canonical := true) <| name.mkStr "ext_iff"
  `(@[ext $(prio)?] protected theorem $extName:ident : ext_type% $flat $struct:ident :=
      fun {..} {..} => by intros; subst_eqs; rfl
    protected theorem $extIffName:ident : ext_iff_type% $flat $struct:ident :=
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
      if tactic.ext.trace.get (← getOptions) then
        let cmd ←`(tactic| apply $(mkIdent (← unresolveNameGlobal lem.declName)))
        usedExtTactics.modify fun x => x.push cmd
      return ← goal.apply (← mkConstWithFreshMVarLevels lem.declName)
    catch _ => s.restore
  throwError "no applicable extensionality lemma found for{indentExpr ty}"

/-- Apply a single extensionality lemma to the current goal. -/
elab "apply_ext_lemma" : tactic => do
  usedExtTactics.modify fun _ => #[]
  liftMetaTactic applyExtLemma
  if tactic.ext.trace.get (← getOptions) then
    let x ← usedExtTactics.get
    let cmd ←`(tactic| · $x*)
    addSuggestion (← MonadLog.getRef) cmd

/--
Postprocessor for `withExt` which runs `rintro` with the given patterns when the target is a
pi type.
-/
def tryIntros [Monad m] [MonadQuotation m] [MonadOptions m] [MonadLiftT (ST IO.RealWorld) m]
    [MonadLiftT TermElabM m] (g : MVarId) (pats : List (TSyntax `rcasesPat))
    (k : MVarId → List (TSyntax `rcasesPat) → m Unit) : m Unit := do
  match pats with
  | [] =>
    if tactic.ext.trace.get (← getOptions) ∧
        (← (g.withContext g.getType' : TermElabM _)).isForall then
      let cmd ←`(tactic| intros)
      usedExtTactics.modify fun x => x.push cmd
    k (← (g.intros : TermElabM _)).2 []
  | p::ps =>
    if (← (g.withContext g.getType' : TermElabM _)).isForall then
      if tactic.ext.trace.get (← getOptions) then
        let cmd ←`(tactic| rintro $(p))
        usedExtTactics.modify fun x => x.push cmd
      for g in ← RCases.rintro #[p] none g do
        k g ps
    else k g pats

/--
Applies a single extensionality lemma, using `pats` to introduce variables in the result.
Runs continuation `k` on each subgoal.
-/
def withExt1 [Monad m] [MonadOptions m] [MonadQuotation m] [MonadLiftT (ST IO.RealWorld) m]
    [MonadLiftT TermElabM m] (g : MVarId) (pats : List (TSyntax `rcasesPat))
    (k : MVarId → List (TSyntax `rcasesPat) → m Unit) : m Unit := do
  for g in ← (applyExtLemma g : TermElabM _) do
    tryIntros g pats k

/--
Applies a extensionality lemmas recursively, using `pats` to introduce variables in the result.
Runs continuation `k` on each subgoal.
-/
def withExtN [Monad m] [MonadOptions m] [MonadQuotation m] [MonadLiftT (ST IO.RealWorld) m]
    [MonadLiftT TermElabM m] [MonadExcept Exception m] (g : MVarId)
    (pats : List (TSyntax `rcasesPat)) (k : MVarId → List (TSyntax `rcasesPat) → m Unit)
    (depth := 1000000) (failIfUnchanged := true) : m Unit :=
  match depth with
  | 0 => k g pats
  | depth+1 => do
    if failIfUnchanged then
      withExt1 g pats fun g pats => withExtN g pats k depth (failIfUnchanged := false)
    else try
      withExt1 g pats fun g pats => withExtN g pats k depth (failIfUnchanged := false)
    catch _ =>
      if tactic.ext.trace.get (← getOptions) then
        let cmd ←`(tactic| sorry)
        usedExtTactics.modify fun x => x.push cmd
      k g pats

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
* `ext1 pat*`: Equivalent to `ext pat* : 1`. Apply only one extensionality lemma.
* `ext?`, `ext1?`: display suggestion to recreate the `ext` application.
-/
syntax (name := tacticExt) "ext" (colGt ppSpace rintroPat)* (" : " num)? : tactic
elab_rules : tactic
  | `(tactic| ext $pats* $[: $n]?) => do
    usedExtTactics.modify fun _ => #[]
    let pats := RCases.expandRIntroPats pats
    let depth := n.map (·.getNat) |>.getD 1000000
    let gs ← extCore (← getMainGoal) pats.toList depth
    replaceMainGoal <| gs.map (·.1) |>.toList
    if tactic.ext.trace.get (← getOptions) then
      let x ← usedExtTactics.get
      let cmd ←`(tactic| · $x*)
      addSuggestion (← MonadLog.getRef) cmd

@[inherit_doc tacticExt]
macro "ext1" xs:(colGt ppSpace rintroPat)* : tactic =>
  if xs.isEmpty then `(tactic| apply_ext_lemma <;> intros)
  else `(tactic| apply_ext_lemma <;> rintro $xs*)

@[inherit_doc tacticExt]
syntax (name := ext1Trace) "ext1?" (colGt ppSpace rintroPat)* : tactic

@[inherit_doc tacticExt]
syntax (name := extTrace) "ext?" (colGt ppSpace rintroPat)* (" : " num)? : tactic

macro_rules
  | `(tactic| ext? $pats* $[: $n]?) =>
    `(tactic| set_option tactic.ext.trace true in
      ext $pats* $[: $n]?)
  | `(tactic| ext1? $pats* ) =>
    `(tactic| set_option tactic.ext.trace true in
      ext1 $pats*)

end Std.Tactic.Ext

attribute [ext] funext propext

@[ext] protected theorem PUnit.ext (x y : PUnit) : x = y := rfl
protected theorem Unit.ext (x y : Unit) : x = y := rfl

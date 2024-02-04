/-
Copyright (c) 2023 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Std.Tactic.Omega.Core
import Std.Tactic.Omega.LinearCombo
import Std.Tactic.Omega.Logic
import Std.Tactic.Omega.Int
import Std.Tactic.FalseOrByContra
import Std.Lean.Meta.Basic
import Std.Lean.Elab.Tactic

/-!
# Frontend to the `omega` tactic.

See `Std.Tactic.Omega` for an overview of the tactic.
-/

open Lean Meta

namespace Std.Tactic.Omega

/--
A partially processed `omega` context.

We have:
* a `Problem` representing the integer linear constraints extracted so far, and their proofs
* the unprocessed `facts : List Expr` taken from the local context,
* the unprocessed `disjunctions : List Expr`,
  which will only be split one at a time if we can't otherwise find a contradiction.

We begin with `facts := ← getLocalHyps` and `problem := .trivial`,
and progressively process the facts.

As we process the facts, we may generate additional facts
(e.g. about coercions and integer divisions).
To avoid duplicates, we maintain a `HashSet` of previously processed facts.
-/
structure MetaProblem where
  /-- An integer linear arithmetic problem. -/
  problem : Problem := {}
  /-- Pending facts which have not been processed yet. -/
  facts : List Expr := []
  /--
  Pending disjunctions, which we will case split one at a time if we can't get a contradiction.
  -/
  disjunctions : List Expr := []
  /-- Facts which have already been processed; we keep these to avoid duplicates. -/
  processedFacts : HashSet Expr := ∅

/-- Construct the `rfl` proof that `lc.eval atoms = e`. -/
def mkEvalRflProof (e : Expr) (lc : LinearCombo) : OmegaM Expr := do
  mkEqReflWithExpectedType e (mkApp2 (.const ``LinearCombo.eval []) (toExpr lc) (← atomsCoeffs))

/-- If `e : Expr` is the `n`-th atom, construct the proof that
`e = (coordinate n).eval atoms`. -/
def mkCoordinateEvalAtomsEq (e : Expr) (n : Nat) : OmegaM Expr := do
  if n < 10 then
    let atoms := (← getThe State).atoms
    let tail ← mkListLit (.const ``Int []) atoms[n+1:].toArray.toList
    let lem := .str ``LinearCombo s!"coordinate_eval_{n}"
    mkEqSymm (mkAppN (.const lem []) (atoms[:n+1].toArray.push tail))
  else
    let atoms ← atomsCoeffs
    let n := toExpr n
    -- Construct the `rfl` proof that `e = (atoms.get? n).getD 0`
    let eq ← mkEqReflWithExpectedType e (mkApp2 (.const ``Coeffs.get []) atoms n)
    mkEqTrans eq (← mkEqSymm (mkApp2 (.const ``LinearCombo.coordinate_eval []) n atoms))

/-- Construct the linear combination (and its associated proof and new facts) for an atom. -/
def mkAtomLinearCombo (e : Expr) : OmegaM (LinearCombo × OmegaM Expr × HashSet Expr) := do
  let (n, facts) ← lookup e
  return ⟨LinearCombo.coordinate n, mkCoordinateEvalAtomsEq e n, facts.getD ∅⟩

-- This has been PR'd as
-- https://github.com/leanprover/lean4/pull/2900
-- and can be removed when that is merged.
@[inherit_doc mkAppN]
local macro_rules
  | `(mkAppN $f #[$xs,*]) => (xs.getElems.foldlM (fun x e => `(Expr.app $x $e)) f : MacroM Term)

mutual

/--
Wrapper for `asLinearComboImpl`,
using a cache for previously visited expressions.

Gives a small (10%) speedup in testing.
I tried using a pointer based cache,
but there was never enough subexpression sharing to make it effective.
-/
partial def asLinearCombo (e : Expr) : OmegaM (LinearCombo × OmegaM Expr × HashSet Expr) := do
  let cache ← get
  match cache.find? e with
  | some (lc, prf) =>
    trace[omega] "Found in cache: {e}"
    return (lc, prf, ∅)
  | none =>
    let r ← asLinearComboImpl e
    modifyThe Cache fun cache => (cache.insert e (r.1, r.2.1.run' cache))
    pure r

/--
Translates an expression into a `LinearCombo`.
Also returns:
* a proof that this linear combo evaluated at the atoms is equal to the original expression
* a list of new facts which should be recorded:
  * for each new atom `a` of the form `((x : Nat) : Int)`, the fact that `0 ≤ a`
  * for each new atom `a` of the form `x / k`, for `k` a positive numeral, the facts that
    `k * a ≤ x < (k + 1) * a`
  * for each new atom of the form `((a - b : Nat) : Int)`, the fact:
    `b ≤ a ∧ ((a - b : Nat) : Int) = a - b ∨ a < b ∧ ((a - b : Nat) : Int) = 0`

We also transform the expression as we descend into it:
* pushing coercions: `↑(x + y)`, `↑(x * y)`, `↑(x / k)`, `↑(x % k)`, `↑k`
* unfolding `emod`: `x % k` → `x - x / k`
-/
partial def asLinearComboImpl (e : Expr) : OmegaM (LinearCombo × OmegaM Expr × HashSet Expr) := do
  trace[omega] "processing {e}"
  match e.int? with
  | some i =>
    let lc := {const := i}
    return ⟨lc, mkEvalRflProof e lc, ∅⟩
  | none =>
    if e.isFVar then
      if let some v ← e.fvarId!.getValue? then
        rewrite e (← mkEqReflWithExpectedType e v)
      else
        mkAtomLinearCombo e
    else match e.getAppFnArgs with
  | (``HAdd.hAdd, #[_, _, _, _, e₁, e₂]) => do
    let (l₁, prf₁, facts₁) ← asLinearCombo e₁
    let (l₂, prf₂, facts₂) ← asLinearCombo e₂
    let prf : OmegaM Expr := do
      let add_eval :=
        mkApp3 (.const ``LinearCombo.add_eval []) (toExpr l₁) (toExpr l₂) (← atomsCoeffs)
      mkEqTrans
        (← mkAppM ``Int.add_congr #[← prf₁, ← prf₂])
        (← mkEqSymm add_eval)
    pure (l₁ + l₂, prf, facts₁.merge facts₂)
  | (``HSub.hSub, #[_, _, _, _, e₁, e₂]) => do
    let (l₁, prf₁, facts₁) ← asLinearCombo e₁
    let (l₂, prf₂, facts₂) ← asLinearCombo e₂
    let prf : OmegaM Expr := do
      let sub_eval :=
        mkApp3 (.const ``LinearCombo.sub_eval []) (toExpr l₁) (toExpr l₂) (← atomsCoeffs)
      mkEqTrans
        (← mkAppM ``Int.sub_congr #[← prf₁, ← prf₂])
        (← mkEqSymm sub_eval)
    pure (l₁ - l₂, prf, facts₁.merge facts₂)
  | (``Neg.neg, #[_, _, e']) => do
    let (l, prf, facts) ← asLinearCombo e'
    let prf' : OmegaM Expr := do
      let neg_eval := mkApp2 (.const ``LinearCombo.neg_eval []) (toExpr l) (← atomsCoeffs)
      mkEqTrans
        (← mkAppM ``Int.neg_congr #[← prf])
        (← mkEqSymm neg_eval)
    pure (-l, prf', facts)
  | (``HMul.hMul, #[_, _, _, _, x, y]) =>
    -- If we decide not to expand out the multiplication,
    -- we have to revert the `OmegaM` state so that any new facts about the factors
    -- can still be reported when they are visited elsewhere.
    let r? ← commitWhen do
      let (xl, xprf, xfacts) ← asLinearCombo x
      let (yl, yprf, yfacts) ← asLinearCombo y
      if xl.coeffs.isZero ∨ yl.coeffs.isZero then
        let prf : OmegaM Expr := do
          let h ← mkDecideProof (mkApp2 (.const ``Or [])
            (.app (.const ``Coeffs.isZero []) (toExpr xl.coeffs))
            (.app (.const ``Coeffs.isZero []) (toExpr yl.coeffs)))
          let mul_eval :=
            mkApp4 (.const ``LinearCombo.mul_eval []) (toExpr xl) (toExpr yl) (← atomsCoeffs) h
          mkEqTrans
            (← mkAppM ``Int.mul_congr #[← xprf, ← yprf])
            (← mkEqSymm mul_eval)
        pure (some (LinearCombo.mul xl yl, prf, xfacts.merge yfacts), true)
      else
        pure (none, false)
    match r? with
    | some r => pure r
    | none => mkAtomLinearCombo e
  | (``HMod.hMod, #[_, _, _, _, n, k]) => rewrite e (mkApp2 (.const ``Int.emod_def []) n k)
  | (``HDiv.hDiv, #[_, _, _, _, x, z]) =>
    match intCast? z with
    | some 0 => rewrite e (mkApp (.const ``Int.ediv_zero []) x)
    | some i =>
      if i < 0 then
        rewrite e (mkApp2 (.const ``Int.ediv_neg []) x (toExpr (-i)))
      else
        mkAtomLinearCombo e
    | _ => mkAtomLinearCombo e
  | (``Min.min, #[_, _, a, b]) =>
    if (← cfg).splitMinMax then
      rewrite e (mkApp2 (.const ``Int.min_def []) a b)
    else
      mkAtomLinearCombo e
  | (``Max.max, #[_, _, a, b]) =>
    if (← cfg).splitMinMax then
      rewrite e (mkApp2 (.const ``Int.max_def []) a b)
    else
      mkAtomLinearCombo e
  | (``Nat.cast, #[.const ``Int [], i, n]) =>
    match n with
    | .fvar h =>
      if let some v ← h.getValue? then
        rewrite e (← mkEqReflWithExpectedType e
          (mkApp3 (.const ``Nat.cast [0]) (.const ``Int []) i v))
      else
        mkAtomLinearCombo e
    | _ => match n.getAppFnArgs with
    | (``Nat.succ, #[n]) => rewrite e (.app (.const ``Int.ofNat_succ []) n)
    | (``HAdd.hAdd, #[_, _, _, _, a, b]) => rewrite e (mkApp2 (.const ``Int.ofNat_add []) a b)
    | (``HMul.hMul, #[_, _, _, _, a, b]) => rewrite e (mkApp2 (.const ``Int.ofNat_mul []) a b)
    | (``HDiv.hDiv, #[_, _, _, _, a, b]) => rewrite e (mkApp2 (.const ``Int.ofNat_ediv []) a b)
    | (``OfNat.ofNat, #[_, n, _]) => rewrite e (.app (.const ``Int.natCast_ofNat []) n)
    | (``HMod.hMod, #[_, _, _, _, a, b]) => rewrite e (mkApp2 (.const ``Int.ofNat_emod []) a b)
    | (``HSub.hSub, #[_, _, _, _, mkAppN (.const ``HSub.hSub _) #[_, _, _, _, a, b], c]) =>
      rewrite e (mkApp3 (.const ``Int.ofNat_sub_sub []) a b c)
    | (``Prod.fst, #[_, β, p]) => match p with
      | .app (.app (.app (.app (.const ``Prod.mk [0, v]) _) _) x) y =>
        rewrite e (mkApp3 (.const ``Int.ofNat_fst_mk [v]) β x y)
      | _ => mkAtomLinearCombo e
    | (``Prod.snd, #[α, _, p]) => match p with
      | .app (.app (.app (.app (.const ``Prod.mk [u, 0]) _) _) x) y =>
        rewrite e (mkApp3 (.const ``Int.ofNat_snd_mk [u]) α x y)
      | _ => mkAtomLinearCombo e
    | (``Min.min, #[_, _, a, b]) => rewrite e (mkApp2 (.const ``Int.ofNat_min []) a b)
    | (``Max.max, #[_, _, a, b]) => rewrite e (mkApp2 (.const ``Int.ofNat_max []) a b)
    | (``Int.natAbs, #[n]) =>
      if (← cfg).splitNatAbs then
        rewrite e (mkApp (.const ``Int.ofNat_natAbs []) n)
      else
        mkAtomLinearCombo e
    | _ => mkAtomLinearCombo e
  | (``Prod.fst, #[α, β, p]) => match p with
    | .app (.app (.app (.app (.const ``Prod.mk [u, v]) _) _) x) y =>
      rewrite e (mkApp4 (.const ``Prod.fst_mk [u, v]) α x β y)
    | _ => mkAtomLinearCombo e
  | (``Prod.snd, #[α, β, p]) => match p with
    | .app (.app (.app (.app (.const ``Prod.mk [u, v]) _) _) x) y =>
      rewrite e (mkApp4 (.const ``Prod.snd_mk [u, v]) α x β y)
    | _ => mkAtomLinearCombo e
  | _ => mkAtomLinearCombo e
where
  /--
  Apply a rewrite rule to an expression, and interpret the result as a `LinearCombo`.
  (We're not rewriting any subexpressions here, just the top level, for efficiency.)
  -/
  rewrite (lhs rw : Expr) : OmegaM (LinearCombo × OmegaM Expr × HashSet Expr) := do
    trace[omega] "rewriting {lhs} via {rw} : {← inferType rw}"
    match (← inferType rw).eq? with
    | some (_, _lhs', rhs) =>
      let (lc, prf, facts) ← asLinearCombo rhs
      let prf' : OmegaM Expr := do mkEqTrans rw (← prf)
      pure (lc, prf', facts)
    | none => panic! "Invalid rewrite rule in 'asLinearCombo'"

end
namespace MetaProblem

/-- The trivial `MetaProblem`, with no facts to processs and a trivial `Problem`. -/
def trivial : MetaProblem where
  problem := {}

instance : Inhabited MetaProblem := ⟨trivial⟩

/--
Add an integer equality to the `Problem`.

We solve equalities as they are discovered, as this often results in an earlier contradiction.
-/
def addIntEquality (p : MetaProblem) (h x : Expr) : OmegaM MetaProblem := do
  let (lc, prf, facts) ← asLinearCombo x
  let newFacts : HashSet Expr := facts.fold (init := ∅) fun s e =>
    if p.processedFacts.contains e then s else s.insert e
  trace[omega] "Adding proof of {lc} = 0"
  pure <|
  { p with
    facts := newFacts.toList ++ p.facts
    problem := ← (p.problem.addEquality lc.const lc.coeffs
      (some do mkEqTrans (← mkEqSymm (← prf)) h)) |>.solveEqualities }

/--
Add an integer inequality to the `Problem`.

We solve equalities as they are discovered, as this often results in an earlier contradiction.
-/
def addIntInequality (p : MetaProblem) (h y : Expr) : OmegaM MetaProblem := do
  let (lc, prf, facts) ← asLinearCombo y
  let newFacts : HashSet Expr := facts.fold (init := ∅) fun s e =>
    if p.processedFacts.contains e then s else s.insert e
  trace[omega] "Adding proof of {lc} ≥ 0"
  pure <|
  { p with
    facts := newFacts.toList ++ p.facts
    problem := ← (p.problem.addInequality lc.const lc.coeffs
      (some do mkAppM ``le_of_le_of_eq #[h, (← prf)])) |>.solveEqualities }

/-- Given a fact `h` with type `¬ P`, return a more useful fact obtained by pushing the negation. -/
def pushNot (h P : Expr) : MetaM (Option Expr) := do
  let P ← whnfR P
  match P with
  | .forallE _ t b _ =>
    if (← isProp t) && (← isProp b) then
     return some (mkApp4 (.const ``Decidable.and_not_of_not_imp []) t b
      (.app (.const ``Classical.propDecidable []) t) h)
    else
      return none
  | .app _ _ =>
    match P.getAppFnArgs with
    | (``LT.lt, #[.const ``Int [], _, x, y]) =>
      return some (mkApp3 (.const ``Int.le_of_not_lt []) x y h)
    | (``LE.le, #[.const ``Int [], _, x, y]) =>
      return some (mkApp3 (.const ``Int.lt_of_not_le []) x y h)
    | (``LT.lt, #[.const ``Nat [], _, x, y]) =>
      return some (mkApp3 (.const ``Nat.le_of_not_lt []) x y h)
    | (``LE.le, #[.const ``Nat [], _, x, y]) =>
      return some (mkApp3 (.const ``Nat.lt_of_not_le []) x y h)
    | (``Eq, #[.const ``Nat [], x, y]) =>
      return some (mkApp3 (.const ``Nat.lt_or_gt_of_ne []) x y h)
    | (``Eq, #[.const ``Int [], x, y]) =>
      return some (mkApp3 (.const ``Int.lt_or_gt_of_ne []) x y h)
    | (``Prod.Lex, _) => return some (← mkAppM ``Prod.of_not_lex #[h])
    | (``Dvd.dvd, #[.const ``Nat [], _, k, x]) =>
      return some (mkApp3 (.const ``Nat.emod_pos_of_not_dvd []) k x h)
    | (``Dvd.dvd, #[.const ``Int [], _, k, x]) =>
      -- This introduces a disjunction that could be avoided by checking `k ≠ 0`.
      return some (mkApp3 (.const ``Int.emod_pos_of_not_dvd []) k x h)
    | (``Or, #[P₁, P₂]) => return some (mkApp3 (.const ``and_not_not_of_not_or []) P₁ P₂ h)
    | (``And, #[P₁, P₂]) =>
      return some (mkApp5 (.const ``Decidable.or_not_not_of_not_and []) P₁ P₂
        (.app (.const ``Classical.propDecidable []) P₁)
        (.app (.const ``Classical.propDecidable []) P₂) h)
    | (``Not, #[P']) =>
      return some (mkApp3 (.const ``Decidable.of_not_not []) P'
        (.app (.const ``Classical.propDecidable []) P') h)
    | (``Iff, #[P₁, P₂]) =>
      return some (mkApp5 (.const ``Decidable.and_not_or_not_and_of_not_iff []) P₁ P₂
        (.app (.const ``Classical.propDecidable []) P₁)
        (.app (.const ``Classical.propDecidable []) P₂) h)
    | _ => return none
  | _ => return none

/--
Parse an `Expr` and extract facts, also returning the number of new facts found.
-/
partial def addFact (p : MetaProblem) (h : Expr) : OmegaM (MetaProblem × Nat) := do
  if ! p.problem.possible then
    return (p, 0)
  else
    let t ← instantiateMVars (← whnfR (← inferType h))
    trace[omega] "adding fact: {t}"
    match t with
    | .forallE _ x y _ =>
      if (← isProp x) && (← isProp y) then
        p.addFact (mkApp4 (.const ``Decidable.not_or_of_imp []) x y
          (.app (.const ``Classical.propDecidable []) x) h)
      else
        return (p, 0)
    | .app _ _ =>
      match t.getAppFnArgs with
      | (``Eq, #[.const ``Int [], x, y]) =>
        match y.int? with
        | some 0 => pure (← p.addIntEquality h x, 1)
        | _ => p.addFact (mkApp3 (.const ``Int.sub_eq_zero_of_eq []) x y h)
      | (``LE.le, #[.const ``Int [], _, x, y]) =>
        match x.int? with
        | some 0 => pure (← p.addIntInequality h y, 1)
        | _ => p.addFact (mkApp3 (.const ``Int.sub_nonneg_of_le []) y x h)
      | (``LT.lt, #[.const ``Int [], _, x, y]) =>
        p.addFact (mkApp3 (.const ``Int.add_one_le_of_lt []) x y h)
      | (``GT.gt, #[.const ``Int [], _, x, y]) =>
        p.addFact (mkApp3 (.const ``Int.lt_of_gt []) x y h)
      | (``GE.ge, #[.const ``Int [], _, x, y]) =>
        p.addFact (mkApp3 (.const ``Int.le_of_ge []) x y h)
      | (``GT.gt, #[.const ``Nat [], _, x, y]) =>
        p.addFact (mkApp3 (.const ``Nat.lt_of_gt []) x y h)
      | (``GE.ge, #[.const ``Nat [], _, x, y]) =>
        p.addFact (mkApp3 (.const ``Nat.le_of_ge []) x y h)
      | (``Ne, #[.const ``Nat [], x, y]) =>
        p.addFact (mkApp3 (.const ``Nat.lt_or_gt_of_ne []) x y h)
      | (``Not, #[P]) => match ← pushNot h P with
        | none => return (p, 0)
        | some h' => p.addFact h'
      | (``Eq, #[.const ``Nat [], x, y]) =>
        p.addFact (mkApp3 (.const ``Int.ofNat_congr []) x y h)
      | (``LT.lt, #[.const ``Nat [], _, x, y]) =>
        p.addFact (mkApp3 (.const ``Int.ofNat_lt_of_lt []) x y h)
      | (``LE.le, #[.const ``Nat [], _, x, y]) =>
        p.addFact (mkApp3 (.const ``Int.ofNat_le_of_le []) x y h)
      | (``Ne, #[.const ``Int [], x, y]) =>
        p.addFact (mkApp3 (.const ``Int.lt_or_gt_of_ne []) x y h)
      | (``Prod.Lex, _) => p.addFact (← mkAppM ``Prod.of_lex #[h])
      | (``Dvd.dvd, #[.const ``Nat [], _, k, x]) =>
        p.addFact (mkApp3 (.const ``Nat.mod_eq_zero_of_dvd []) k x h)
      | (``Dvd.dvd, #[.const ``Int [], _, k, x]) =>
        p.addFact (mkApp3 (.const ``Int.mod_eq_zero_of_dvd []) k x h)
      | (``And, #[t₁, t₂]) => do
          let (p₁, n₁) ← p.addFact (mkApp3 (.const ``And.left []) t₁ t₂ h)
          let (p₂, n₂) ← p₁.addFact (mkApp3 (.const ``And.right []) t₁ t₂ h)
          return (p₂, n₁ + n₂)
      | (``Exists, #[α, P]) =>
        p.addFact (mkApp3 (.const ``Exists.choose_spec [← getLevel α]) α P h)
      | (``Subtype, #[α, P]) =>
        p.addFact (mkApp3 (.const ``Subtype.property [← getLevel α]) α P h)
      | (``Iff, #[P₁, P₂]) =>
        p.addFact (mkApp4 (.const ``Decidable.and_or_not_and_not_of_iff [])
          P₁ P₂ (.app (.const ``Classical.propDecidable []) P₂) h)
      | (``Or, #[_, _]) =>
        if (← cfg).splitDisjunctions then
          return ({ p with disjunctions := p.disjunctions.insert h }, 1)
        else
          return (p, 0)
      | _ => pure (p, 0)
    | _ => pure (p, 0)

/--
Process all the facts in a `MetaProblem`, returning the new problem, and the number of new facts.

This is partial because new facts may be generated along the way.
-/
partial def processFacts (p : MetaProblem) : OmegaM (MetaProblem × Nat) := do
  match p.facts with
  | [] => pure (p, 0)
  | h :: t =>
    if p.processedFacts.contains h then
      processFacts { p with facts := t }
    else
      let (p₁, n₁) ← MetaProblem.addFact { p with
        facts := t
        processedFacts := p.processedFacts.insert h } h
      let (p₂, n₂) ← p₁.processFacts
      return (p₂, n₁ + n₂)

end MetaProblem

/--
Given `p : P ∨ Q` (or any inductive type with two one-argument constructors),
split the goal into two subgoals:
one containing the hypothesis `h : P` and another containing `h : Q`.
-/
def cases₂ (mvarId : MVarId) (p : Expr) (hName : Name := `h) :
    MetaM ((MVarId × FVarId) × (MVarId × FVarId)) := do
  let mvarId ← mvarId.assert `hByCases (← inferType p) p
  let (fvarId, mvarId) ← mvarId.intro1
  let #[s₁, s₂] ← mvarId.cases fvarId #[{ varNames := [hName] }, { varNames := [hName] }] |
    throwError "'cases' tactic failed, unexpected number of subgoals"
  let #[Expr.fvar f₁ ..] ← pure s₁.fields
    | throwError "'cases' tactic failed, unexpected new hypothesis"
  let #[Expr.fvar f₂ ..] ← pure s₂.fields
    | throwError "'cases' tactic failed, unexpected new hypothesis"
  return ((s₁.mvarId, f₁), (s₂.mvarId, f₂))


mutual

/--
Split a disjunction in a `MetaProblem`, and if we find a new usable fact
call `omegaImpl` in both branches.
-/
partial def splitDisjunction (m : MetaProblem) (g : MVarId) : OmegaM Unit := g.withContext do
  match m.disjunctions with
    | [] => throwError "omega did not find a contradiction:\n{m.problem}"
    | h :: t =>
      trace[omega] "Case splitting on {← inferType h}"
      let ctx ← getMCtx
      let (⟨g₁, h₁⟩, ⟨g₂, h₂⟩) ← cases₂ g h
      trace[omega] "Adding facts:\n{← g₁.withContext <| inferType (.fvar h₁)}"
      let m₁ := { m with facts := [.fvar h₁], disjunctions := t }
      let r ← withoutModifyingState do
        let (m₁, n) ← g₁.withContext m₁.processFacts
        if 0 < n then
          omegaImpl m₁ g₁
          pure true
        else
          pure false
      if r then
        trace[omega] "Adding facts:\n{← g₂.withContext <| inferType (.fvar h₂)}"
        let m₂ := { m with facts := [.fvar h₂], disjunctions := t }
        omegaImpl m₂ g₂
      else
        trace[omega] "No new facts found."
        setMCtx ctx
        splitDisjunction { m with disjunctions := t } g

/-- Implementation of the `omega` algorithm, and handling disjunctions. -/
partial def omegaImpl (m : MetaProblem) (g : MVarId) : OmegaM Unit := g.withContext do
  let (m, _) ← m.processFacts
  guard m.facts.isEmpty
  let p := m.problem
  trace[omega] "Extracted linear arithmetic problem:\nAtoms: {← atomsList}\n{p}"
  let p' ← if p.possible then p.elimination else pure p
  trace[omega] "After elimination:\nAtoms: {← atomsList}\n{p'}"
  match p'.possible, p'.proveFalse?, p'.proveFalse?_spec with
  | true, _, _ =>
    splitDisjunction m g
  | false, .some prf, _ =>
    trace[omega] "Justification:\n{p'.explanation?.get}"
    let prf ← instantiateMVars (← prf)
    trace[omega] "omega found a contradiction, proving {← inferType prf}"
    trace[omega] "{prf}"
    g.assign prf

end

/--
Given a collection of facts, try prove `False` using the omega algorithm,
and close the goal using that.
-/
def omega (facts : List Expr) (g : MVarId) (cfg : OmegaConfig := {}) : MetaM Unit :=
  OmegaM.run (omegaImpl { facts } g) cfg

open Lean Elab Tactic Parser.Tactic

/-- The `omega` tactic, for resolving integer and natural linear arithmetic problems. -/
def omegaTactic (cfg : OmegaConfig) : TacticM Unit := do
  liftMetaFinishingTactic fun g => do
    let g ← falseOrByContra g
      (useClassical := false) -- because all the hypotheses we can make use of are decidable
    g.withContext do
      let hyps := (← getLocalHyps).toList
      trace[omega] "analyzing {hyps.length} hypotheses:\n{← hyps.mapM inferType}"
      omega hyps g cfg

/-- The `omega` tactic, for resolving integer and natural linear arithmetic problems. This
`TacticM Unit` frontend with default configuration can be used as an Aesop rule, for example via
the tactic call `aesop (add 50% tactic Std.Tactic.Omega.omegaDefault)`. -/
def omegaDefault : TacticM Unit := omegaTactic {}

/--
The `omega` tactic, for resolving integer and natural linear arithmetic problems.

It is not yet a full decision procedure (no "dark" or "grey" shadows),
but should be effective on many problems.

We handle hypotheses of the form `x = y`, `x < y`, `x ≤ y`, and `k ∣ x` for `x y` in `Nat` or `Int`
(and `k` a literal), along with negations of these statements.

We decompose the sides of the inequalities as linear combinations of atoms.

If we encounter `x / k` or `x % k` for literal integers `k` we introduce new auxiliary variables
and the relevant inequalities.

On the first pass, we do not perform case splits on natural subtraction.
If `omega` fails, we recursively perform a case split on
a natural subtraction appearing in a hypothesis, and try again.

The options
```
omega (config :=
  { splitDisjunctions := true, splitNatSub := true, splitNatAbs := true, splitMinMax := true })
```
can be used to:
* `splitDisjunctions`: split any disjunctions found in the context,
  if the problem is not otherwise solvable.
* `splitNatSub`: for each appearance of `((a - b : Nat) : Int)`, split on `a ≤ b` if necessary.
* `splitNatAbs`: for each appearance of `Int.natAbs a`, split on `0 ≤ a` if necessary.
* `splitMinMax`: for each occurrence of `min a b`, split on `min a b = a ∨ min a b = b`
Currently, all of these are on by default.
-/
syntax (name := omegaSyntax) "omega" (config)? : tactic

elab_rules : tactic |
    `(tactic| omega $[$cfg]?) => do
  let cfg ← elabOmegaConfig (mkOptionalNode cfg)
  omegaTactic cfg

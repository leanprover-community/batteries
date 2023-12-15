/-
Copyright (c) 2023 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Std.Tactic.Omega.Core
import Std.Tactic.Omega.LinearCombo
import Std.Tactic.Omega.Logic
import Std.Tactic.Omega.Int
import Std.Lean.Meta.Basic
import Std.Lean.Elab.Tactic

/-!
# `omega`

This is an implementation of the `omega` algorithm, currently without "dark" and "grey" shadows,
although the framework should be compatible with adding that part of the algorithm later.

The implementation closely follows William Pugh's
"The omega test: a fast and practical integer programming algorithm for dependence analysis"
https://doi.org/10.1145/125826.125848.

The `MetaM` level `omega` tactic takes a `List Expr` of facts,
and tries to discharge the goal by proving `False`.

The user-facing `omega` tactic first calls `false_or_by_contra`, and then invokes the `omega` tactic
on all hypotheses.

### Pre-processing

In the `false_or_by_contra` step, we:
* if the goal is `False`, do nothing,
* if the goal is `¬ P`, introduce `P`,
* if the goal is `x ≠ y`, introduce `x = y`,
* otherwise, for a goal `P`, replace it with `¬ ¬ P` and introduce `¬ P`.

The `omega` tactic pre-processes the hypotheses in the following ways:
* Replace `x > y` for `x y : Nat` or `x y : Int` with `x ≥ y + 1`.
* Given `x ≥ y` for `x : Nat`, replace it with `(x : Int) ≥ (y : Int)`.
* Push `Nat`-to-`Int` coercions inwards across `+`, `*`, `/`, `%`.
* Replace `k ∣ x` for a literal `k : Nat` with `x % k = 0`,
  and replace `¬ k ∣ x` with `x % k > 0`.
* If `x / m` appears, for some `x : Int` and literal `m : Nat`,
  replace `x / m` with a new variable `α` and add the constraints
  `0 ≤ - m * α + x ≤ m - 1`.
* If `x % m` appears, similarly, introduce the same new contraints
  but replace `x % m` with `- m * α + x`.
* Split conjunctions, existentials, and subtypes.
* Record, for each appearance of `(a - b : Int)` with `a b : Nat`, the disjunction
  `b ≤ a ∧ ((a - b : Nat) : Int) = a - b ∨ a < b ∧ ((a - b : Nat) : Int) = 0`.
  We don't immediately split this; see the discussion below for how disjunctions are handled.

After this preprocessing stage, we have a collection of linear inequalities
(all using `≤` rather than `<`) and equalities in some set of atoms.

TODO: We should identify atoms up to associativity and commutativity,
so that `omega` can handle problems such as `a * b < 0 && b * a > 0 → False`.
This should be a relatively easy modification of the `lookup` function in `OmegaM`.
After doing so, we could allow the preprocessor to distribute multiplication over addition.

### Normalization

Throughout the remainder of the algorithm, we apply the following normalization steps to
all linear constraints:
* Make the leading coefficient positive (thus giving us both upper and lower bounds).
* Divide through by the GCD of the coefficients, rounding the constant terms appropriately.
* Whenever we have both an upper and lower bound for the same coefficients,
  check they are compatible. If they are tight, mark the pair of constraints as an equality.
  If they are inconsistent, stop further processing.

### Solving equalities

The next step is to solve all equalities.

We first solve any equalities that have a `±1` coefficient;
these allow us to eliminate that variable.

After this, there may be equalities remaining with all coefficients having absolute value greater
than one. We select an equality `c₀ + ∑ cᵢ * xᵢ = 0` with smallest minimal absolute value
of the `cᵢ`, breaking ties by preferring equalities with smallest maximal absolute value.
We let `m = ∣cⱼ| + 1` where `cⱼ` is the coefficient with smallest absolute value..
We then add the new equality `(bmod c₀ m) + ∑ (bmod cᵢ m) xᵢ = m α` with `α` being a new variable.
Here `bmod` is "balanced mod", taking values in `[- m/2, (m - 1)/2]`.
This equality holds (for some value of `α`) because the left hand side differs from the left hand
side of the original equality by a multiple of `m`.
Moreover, in this equality the coefficient of `xⱼ` is `±1`, so we can solve and eliminate `xⱼ`.

So far this isn't progress: we've introduced a new variable and eliminated a variable.
However, this process terminates, as the pair `(c, C)` lexicographically decreases,
where `c` is the smallest minimal absolute value and `C` is the smallest maximal absolute value
amongst those equalities with minimal absolute value `c`.
(Happily because we're running this in metaprogramming code, we don't actually need to prove this
termination! If we later want to upgrade to a decision procedure, or to produce counterexamples
we would need to do this. It's certainly possible, and existed in an earlier prototype version.)

### Solving inequalities

After solving all equalities, we turn to the inequalities.

We need to select a variable to eliminate; this choice is discussed below.

#### Shadows

The omega algorithm indicates we should consider three subproblems,
called the "real", "dark", and "grey" shadows.
(In fact the "grey" shadow is a disjunction of potentially many problems.)
Our problem is satisfiable if and only if the real shadow is satisfiable
and either the dark or grey shadow is satisfiable.

Currently we do not implement either the dark or grey shadows, and thus if the real shadow is
satisfiable we must fail, and report that we couldn't find a contradiction, even though the
problem may be unsatisfiable.

In practical problems, it appears to be relatively rare that we fail because of not handling the
dark and grey shadows.

Fortunately, in many cases it is possible to choose a variable to eliminate such that
the real and dark shadows coincide, and the grey shadows are empty. In this situation
we don't lose anything by ignoring the dark and grey shadows.
We call this situation an exact elimination.
A sufficient condition for exactness is that either all upper bounds on `xᵢ` have unit coefficient,
or all lower bounds on `xᵢ` has unit coefficient.
We always prefer to select the value of `i` so that this condition holds, if possible.
We break ties by preferring to select a value of `i` that minimizes the number of new constraints
introduced in the real shadow.

#### The real shadow: Fourier-Motzkin elimination

The real shadow for a variable `i` is just the Fourier-Motzkin elimination.

We begin discard all inequalities involving the variable `i`.

Then, for each pair of constraints `f ≤ c * xᵢ` and `c' * xᵢ ≤ f'`
with both `c` and `c'` positive (i.e. for each pair of an lower and upper bound on `xᵢ`)
we introduce the new constraint `c * f' - c' * f ≥ 0`.

(Note that if there are only upper bounds on `xᵢ`, or only lower bounds on `xᵢ` this step
simply discards inequalities.)

#### The dark and grey shadows

For each such new constraint `c' * f - c * f' ≤ 0`, we either have the strengthening
`c * f' - c' * f ≥ c * c' - c - c' + 1`
or we do not, i.e.
`c * f' - c' * f ≤ c * c' - c - c'`.
In the latter case, combining this inequality with `f' ≥ c' * xᵢ` we obtain
`c' * (c * xᵢ - f) ≤ c * c' - c - c'`
and as we already have `c * xᵢ - f ≥ 0`,
we conclude that `c * xᵢ - f = j` for some `j = 0, 1, ..., (c * c' - c - c')/c'`
(with, as usual the division rounded down).

Note that the largest possible value of `j` occurs with `c'` is as large as possible.

Thus the "dark" shadow is the variant of the real shadow where we replace each new inequality
with its strengthening.
The "grey" shadows are the union of the problems obtained by taking
a lower bound `f ≤ c * xᵢ` for `xᵢ` and some `j = 0, 1, ..., (c * m - c - m)/m`, where `m`
is the largest coefficient `c'` appearing in an upper bound `c' * xᵢ ≤ f'` for `xᵢ`,
and adding to the original problem (i.e. without doing any Fourier-Motzkin elimination) the single
new equation `c * xᵢ - f = j`, and the inequalities
`c * xᵢ - f > (c * m - c - m)/m` for each previously considered lower bound.

As stated above, the satisfiability of the original problem is in fact equivalent to
the satisfiability of the real shadow, *and* the satisfiability of *either* the dark shadow,
or at least one of the grey shadows.

TODO: implement the dark and grey shadows!

### Disjunctions

The omega algorithm as described above accumulates various disjunctions,
either coming from natural subtraction, or from the dark and grey shadows.

When we encounter such a disjunction, we store it in a list of disjunctions,
but do not immediately split it.

Instead we first try to find a contradiction (i.e. by eliminating equalities and inequalities)
without the disjunctive hypothesis.
If this fails, we then retrieve the first disjunction from the list, split it,
and try to find a contradiction in both branches.

(Note that we make no attempt to optimize the order in which we split disjunctions:
it's currently on a first in last out basis.)

The work done eliminating equalities can be reused when splitting disjunctions,
but we need to redo all the work eliminating inequalities in each branch.

## Future work
* Implementation of dark and grey shadows.
* Identification of atoms up to associativity and commutativity of monomials.
* Further optimization.
  * Some data is recomputed unnecessarily, e.g. the GCDs of coefficients.
* Sparse representation of coefficients.
  * I have a branch in which this is implemented, modulo some proofs about algebraic operations
    on sparse arrays.
* Case splitting on `Int.abs`?
-/

open Lean Meta

-- PR'd as https://github.com/leanprover/std4/pull/462
/--
Given `p : P ∨ Q` (or any inductive type with two one-argument constructors),
split the goal into two subgoals:
one containing the hypothesis `h : P` and another containing `h : Q`.
-/
def _root_.Lean.MVarId.cases₂ (mvarId : MVarId) (p : Expr) (hName : Name := `h) :
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

TODO: we may want to solve equalities as we find them.
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

/-- Construct the term with type hint `(Eq.refl a : a = b)`-/
def mkEqReflWithExpectedType (a b : Expr) : MetaM Expr := do
  mkExpectedTypeHint (← mkEqRefl a) (← mkEq a b)

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
  | none => match e.getAppFnArgs with
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
  | (``HMul.hMul, #[_, _, _, _, n, e']) =>
    match intCast? n with
    | some n' =>
      let (l, prf, facts) ← asLinearCombo e'
      let prf' : OmegaM Expr := do
        let smul_eval := mkApp3 (.const ``LinearCombo.smul_eval []) (toExpr l) n (← atomsCoeffs)
        mkEqTrans
          (← mkAppM ``Int.mul_congr_right #[n, ← prf])
          (← mkEqSymm smul_eval)
      pure (l.smul n', prf', facts)
    | none => mkAtomLinearCombo e
  | (``HMod.hMod, #[_, _, _, _, n, k]) => rewrite e (mkApp2 (.const ``Int.emod_def []) n k)
  | (``Nat.cast, #[_, _, n]) => match n.getAppFnArgs with
    | (``HAdd.hAdd, #[_, _, _, _, a, b]) => rewrite e (mkApp2 (.const ``Int.ofNat_add []) a b)
    | (``HMul.hMul, #[_, _, _, _, a, b]) => rewrite e (mkApp2 (.const ``Int.ofNat_mul []) a b)
    | (``HDiv.hDiv, #[_, _, _, _, a, b]) => rewrite e (mkApp2 (.const ``Int.ofNat_ediv []) a b)
    | (``OfNat.ofNat, #[_, n, _]) => rewrite e (.app (.const ``Int.natCast_ofNat []) n)
    | (``HMod.hMod, #[_, _, _, _, a, b]) => rewrite e (mkApp2 (.const ``Int.ofNat_emod []) a b)
    | (``HSub.hSub, #[_, _, _, _, mkAppN (.const ``HSub.hSub _) #[_, _, _, _, a, b], c]) =>
      rewrite e (mkApp3 (.const ``Int.ofNat_sub_sub []) a b c)
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
-/
def addIntInequality (p : MetaProblem) (h y : Expr) : OmegaM MetaProblem := do
  let (lc, prf, facts) ← asLinearCombo y
  let newFacts : HashSet Expr := facts.fold (init := ∅) fun s e =>
    if p.processedFacts.contains e then s else s.insert e
  trace[omega] "Adding proof of {lc} ≥ 0"
  pure <|
  { p with
    facts := newFacts.toList ++ p.facts
    problem := p.problem.addInequality lc.const lc.coeffs
      (some do mkAppM ``le_of_le_of_eq #[h, (← prf)]) }

/-- Given a fact `h` with type `¬ P`, return a more useful fact obtained by pushing the negation. -/
def pushNot (h P : Expr) : Option Expr := do
  match P.getAppFnArgs with
  | (``LT.lt, #[.const ``Int [], _, x, y]) => some (mkApp3 (.const ``Int.le_of_not_lt []) x y h)
  | (``LE.le, #[.const ``Int [], _, x, y]) => some (mkApp3 (.const ``Int.lt_of_not_le []) x y h)
  | (``LT.lt, #[.const ``Nat [], _, x, y]) => some (mkApp3 (.const ``Nat.le_of_not_lt []) x y h)
  | (``LE.le, #[.const ``Nat [], _, x, y]) => some (mkApp3 (.const ``Nat.lt_of_not_le []) x y h)
  | (``GT.gt, #[.const ``Int [], _, x, y]) => some (mkApp3 (.const ``Int.le_of_not_lt []) y x h)
  | (``GE.ge, #[.const ``Int [], _, x, y]) => some (mkApp3 (.const ``Int.lt_of_not_le []) y x h)
  | (``GT.gt, #[.const ``Nat [], _, x, y]) => some (mkApp3 (.const ``Nat.le_of_not_lt []) y x h)
  | (``GE.ge, #[.const ``Nat [], _, x, y]) => some (mkApp3 (.const ``Nat.lt_of_not_le []) y x h)
  | (``Eq, #[.const ``Nat [], x, y]) => some (mkApp3 (.const ``Nat.lt_or_gt_of_ne []) x y h)
  | (``Eq, #[.const ``Int [], x, y]) => some (mkApp3 (.const ``Int.lt_or_gt_of_ne []) x y h)
  | (``Dvd.dvd, #[.const ``Nat [], _, k, x]) =>
    some (mkApp3 (.const ``Nat.emod_pos_of_not_dvd []) k x h)
  | (``Dvd.dvd, #[.const ``Int [], _, k, x]) =>
    -- This introduces a disjunction that could be avoided by checking `k ≠ 0`.
    some (mkApp3 (.const ``Int.emod_pos_of_not_dvd []) k x h)
  | (``Or, #[P₁, P₂]) => some (mkApp3 (.const ``and_not_not_of_not_or []) P₁ P₂ h)
  | (``And, #[P₁, P₂]) =>
    some (mkApp5 (.const ``Decidable.or_not_not_of_not_and []) P₁ P₂
      (.app (.const ``Classical.propDecidable []) P₁)
      (.app (.const ``Classical.propDecidable []) P₂) h)
  | _ => none

/-- Parse an `Expr` and extract facts. -/
partial def addFact (p : MetaProblem) (h : Expr) : OmegaM MetaProblem := do
  if ! p.problem.possible then
    return p
  else
    let t ← instantiateMVars (← inferType h)
    match t with
    | mkAppN (.const ``Eq _) #[.const ``Int [], x, y] =>
      match y.int? with
      | some 0 => p.addIntEquality h x
      | _ => p.addFact (mkApp3 (.const ``Int.sub_eq_zero_of_eq []) x y h)
    | mkAppN (.const ``LE.le _) #[.const ``Int [], _, x, y] =>
      match x.int? with
      | some 0 => p.addIntInequality h y
      | _ => p.addFact (mkApp3 (.const ``Int.sub_nonneg_of_le []) y x h)
    | mkAppN (.const ``LT.lt _) #[.const ``Int [], _, x, y] =>
      p.addFact (mkApp3 (.const ``Int.add_one_le_of_lt []) x y h)
    | mkAppN (.const ``GT.gt _) #[.const ``Int [], _, x, y] =>
      p.addFact (mkApp3 (.const ``Int.lt_of_gt []) x y h)
    | mkAppN (.const ``GE.ge _) #[.const ``Int [], _, x, y] =>
      p.addFact (mkApp3 (.const ``Int.le_of_ge []) x y h)
    | mkAppN (.const ``GT.gt _) #[.const ``Nat [], _, x, y] =>
      p.addFact (mkApp3 (.const ``Nat.lt_of_gt []) x y h)
    | mkAppN (.const ``GE.ge _) #[.const ``Nat [], _, x, y] =>
      p.addFact (mkApp3 (.const ``Nat.le_of_ge []) x y h)
    | mkAppN (.const ``Not _) #[P] => match pushNot h P with
      | none => return p
      | some h' => p.addFact h'
    | mkAppN (.const ``Eq _) #[.const ``Nat [], x, y] =>
      p.addFact (mkApp3 (.const ``Int.ofNat_congr []) x y h)
    | mkAppN (.const ``LT.lt _) #[.const ``Nat [], _, x, y] =>
      p.addFact (mkApp3 (.const ``Int.ofNat_lt_of_lt []) x y h)
    | mkAppN (.const ``LE.le _) #[.const ``Nat [], _, x, y] =>
      p.addFact (mkApp3 (.const ``Int.ofNat_le_of_le []) x y h)
    | mkAppN (.const ``Dvd.dvd _) #[.const ``Nat [], _, k, x] =>
      p.addFact (mkApp3 (.const ``Nat.mod_eq_zero_of_dvd []) k x h)
    | mkAppN (.const ``Dvd.dvd _) #[.const ``Int [], _, k, x] =>
      p.addFact (mkApp3 (.const ``Int.mod_eq_zero_of_dvd []) k x h)
    | mkAppN (.const ``And _) #[t₁, t₂] => do
        (← p.addFact (mkApp3 (.const ``And.left []) t₁ t₂ h)).addFact
          (mkApp3 (.const ``And.right []) t₁ t₂ h)
    | mkAppN (.const ``Exists [u]) #[α, P] =>
      p.addFact (mkApp3 (.const ``Exists.choose_spec [u]) α P h)
    | mkAppN (.const ``Subtype [u]) #[α, P] =>
      p.addFact (mkApp3 (.const ``Subtype.property [u]) α P h)
    | mkAppN (.const ``Or _) #[_, _] => return { p with disjunctions := p.disjunctions.insert h }
    | _ => pure p

/--
Process all the facts in a `MetaProblem`.

This is partial because new facts may be generated along the way.
-/
partial def processFacts (p : MetaProblem) : OmegaM MetaProblem := do
  match p.facts with
  | [] => pure p
  | h :: t =>
    if p.processedFacts.contains h then
      processFacts { p with facts := t }
    else
      (← MetaProblem.addFact { p with
        facts := t
        processedFacts := p.processedFacts.insert h } h).processFacts

end MetaProblem

/-- Implementation of the `omega` algorithm, and handling disjunctions. -/
partial def omegaImpl (m : MetaProblem) (g : MVarId) : OmegaM Unit := g.withContext do
  let m' ← m.processFacts
  guard m'.facts.isEmpty
  let p := m'.problem
  trace[omega] "Extracted linear arithmetic problem:\nAtoms: {← atomsList}\n{p}"
  let p' ← if p.possible then p.solveEqualities else pure p
  let p'' ← if p'.possible then p'.run' else pure p'
  trace[omega] "After elimination:\nAtoms: {← atomsList}\n{p''}"
  if p''.possible then
    match m'.disjunctions with
    | [] => throwError "omega did not find a contradiction:\n{p''}"
    | h :: t =>
      trace[omega] "Case splitting on {← inferType h}"
      let (⟨g₁, h₁⟩, ⟨g₂, h₂⟩) ← g.cases₂ h
      trace[omega] "Adding facts:\n{← g₁.withContext <| inferType (.fvar h₁)}"
      let m₁ := { m' with
        problem := p'
        facts := [.fvar h₁]
        disjunctions := t }
      savingState do omegaImpl m₁ g₁
      trace[omega] "Adding facts:\n{← g₂.withContext <| inferType (.fvar h₂)}"
      let m₂ := { m' with
        problem := p
        facts := [.fvar h₂]
        disjunctions := t }
      omegaImpl m₂ g₂
  else
    match p''.proveFalse? with
    | none => throwError "omega found a contradiction, but didn't produce a proof of False"
    | some prf =>
      trace[omega] "Justification:\n{p''.explanation?.get}"
      let prf ← instantiateMVars (← prf)
      trace[omega] "omega found a contradiction, proving {← inferType prf}"
      trace[omega] "{prf}"
      g.assign prf

/--
Given a collection of facts, try prove `False` using the omega algorithm,
and close the goal using that.
-/
def omega (facts : List Expr) (g : MVarId) : MetaM Unit := OmegaM.run do
  omegaImpl { facts } g

-- `false_or_by_contra` has been PR'd as https://github.com/leanprover/std4/pull/460

/--
Changes the goal to `False`, retaining as much information as possible:

If the goal is `False`, do nothing.
If the goal is `¬ P`, introduce `P`.
If the goal is `x ≠ y`, introduce `x = y`.
Otherwise, for a goal `P`, replace it with `¬ ¬ P` and introduce `¬ P`.
-/
syntax (name := false_or_by_contra) "false_or_by_contra" : tactic

@[inherit_doc false_or_by_contra]
def falseOrByContra (g : MVarId) : MetaM (List MVarId) := do
  match ← g.getType with
  | .const ``False _ => pure [g]
  | .app (.const ``Not _) _
  | mkAppN (.const ``Ne _) #[_, _, _] => pure [(← g.intro1).2]
  | _ => (← g.applyConst ``Classical.byContradiction).mapM fun s => (·.2) <$> s.intro1

open Lean Elab Tactic

elab_rules : tactic
  | `(tactic| false_or_by_contra) => liftMetaTactic falseOrByContra

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
-/
def omegaTactic : TacticM Unit := do
    liftMetaFinishingTactic fun g => do
      let gs ← falseOrByContra g
      _ ← gs.mapM fun g => g.withContext do
        let hyps := (← getLocalHyps).toList
        trace[omega] "analyzing {hyps.length} hypotheses:\n{← hyps.mapM inferType}"
        omega hyps g

@[inherit_doc omegaTactic]
syntax "omega" : tactic

elab_rules : tactic
  | `(tactic| omega) => omegaTactic

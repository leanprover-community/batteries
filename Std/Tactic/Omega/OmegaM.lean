/-
Copyright (c) 2023 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Std.Tactic.Omega.Int
import Std.Tactic.Omega.LinearCombo
import Std.Tactic.Omega.Config
import Std.Lean.Expr
import Std.Lean.HashSet

/-!
# The `OmegaM` state monad.

We keep track of the linear atoms (up to defeq) that have been encountered so far,
and also generate new facts as new atoms are recorded.

The main functions are:
* `atoms : OmegaM (List Expr)` which returns the atoms recorded so far
* `lookup (e : Expr) : OmegaM (Nat × Option (HashSet Expr))` which checks if an `Expr` has
  already been recorded as an atom, and records it.
  `lookup` return the index in `atoms` for this `Expr`.
  The `Option (HashSet Expr)` return value is `none` is the expression has been previously
  recorded, and otherwise contains new facts that should be added to the `omega` problem.
  * for each new atom `a` of the form `((x : Nat) : Int)`, the fact that `0 ≤ a`
  * for each new atom `a` of the form `x / k`, for `k` a positive numeral, the facts that
    `k * a ≤ x < k * a + k`
  * for each new atom of the form `((a - b : Nat) : Int)`, the fact:
    `b ≤ a ∧ ((a - b : Nat) : Int) = a - b ∨ a < b ∧ ((a - b : Nat) : Int) = 0`

The `OmegaM` monad also keeps an internal cache of visited expressions
(not necessarily atoms, but arbitrary subexpressions of one side of a linear relation)
to reduce duplication.
The cache maps `Expr`s to pairs consisting of a `LinearCombo`,
and proof that the expression is equal to the evaluation of the `LinearCombo` at the atoms.
-/

open Lean Meta

namespace Std.Tactic.Omega

/-- Context for the `OmegaM` monad, containing the user configurable options. -/
structure Context where
  /-- User configurable options for `omega`. -/
  cfg : OmegaConfig

/-- The internal state for the `OmegaM` monad, recording previously encountered atoms. -/
structure State where
  /-- The atoms up-to-defeq encountered so far. -/
  atoms : Array Expr := #[]

/-- An intermediate layer in the `OmegaM` monad. -/
abbrev OmegaM' := StateRefT State (ReaderT Context MetaM)

/--
Cache of expressions that have been visited, and their reflection as a linear combination.
-/
def Cache : Type := HashMap Expr (LinearCombo × OmegaM' Expr)

/--
The `OmegaM` monad maintains two pieces of state:
* the linear atoms discovered while processing hypotheses
* a cache mapping subexpressions of one side of a linear inequality to `LinearCombo`s
  (and a proof that the `LinearCombo` evaluates at the atoms to the original expression). -/
abbrev OmegaM := StateRefT Cache OmegaM'

/-- Run a computation in the `OmegaM` monad, starting with no recorded atoms. -/
def OmegaM.run (m : OmegaM α) (cfg : OmegaConfig) : MetaM α :=
  m.run' HashMap.empty |>.run' {} { cfg }

/-- Retrieve the user-specified configuration options. -/
def cfg : OmegaM OmegaConfig := do pure (← read).cfg

/-- Retrieve the list of atoms. -/
def atoms : OmegaM (List Expr) := return (← getThe State).atoms.toList

/-- Return the `Expr` representing the list of atoms. -/
def atomsList : OmegaM Expr := do mkListLit (.const ``Int []) (← atoms)

/-- Return the `Expr` representing the list of atoms as a `Coeffs`. -/
def atomsCoeffs : OmegaM Expr := do
  return .app (.const ``Coeffs.ofList []) (← atomsList)

/-- Run an `OmegaM` computation, restoring the state afterwards depending on the result. -/
def commitWhen (t : OmegaM (α × Bool)) : OmegaM α := do
  let state ← getThe State
  let cache ← getThe Cache
  let (a, r) ← t
  if !r then do
    modifyThe State fun _ => state
    modifyThe Cache fun _ => cache
  pure a

/--
Run an `OmegaM` computation, restoring the state afterwards.
-/
def withoutModifyingState (t : OmegaM α) : OmegaM α :=
  commitWhen (do pure (← t, false))

/-- Wrapper around `Expr.nat?` that also allows `Nat.cast`. -/
def natCast? (n : Expr) : Option Nat :=
  match n.getAppFnArgs with
  | (``Nat.cast, #[_, _, n]) => n.nat?
  | _ => n.nat?

/-- Wrapper around `Expr.int?` that also allows `Nat.cast`. -/
def intCast? (n : Expr) : Option Int :=
  match n.getAppFnArgs with
  | (``Nat.cast, #[_, _, n]) => n.nat?
  | _ => n.int?

/--
Analyzes a newly recorded atom,
returning a collection of interesting facts about it that should be added to the context.
-/
def analyzeAtom (e : Expr) : OmegaM (HashSet Expr) := do
  match e.getAppFnArgs with
  | (``Nat.cast, #[_, _, e']) =>
    -- Casts of natural numbers are non-negative.
    let mut r := {Expr.app (.const ``Int.ofNat_nonneg []) e'}
    match (← cfg).splitNatSub, (← cfg).splitNatAbs, e'.getAppFnArgs with
      | true, _, (``HSub.hSub, #[_, _, _, _, a, b]) =>
        -- `((a - b : Nat) : Int)` gives a dichotomy
        r := r.insert (mkApp2 (.const ``Int.ofNat_sub_dichotomy []) a b)
      | _, true, (``Int.natAbs, #[x]) =>
        -- `(a.natAbs : Int)` gives a dichotomy
        r := r.insert (mkApp (.const ``Int.natAbs_dichotomy []) x)
      | _, _,_ => pure ()
    return r
  | (``HDiv.hDiv, #[_, _, _, _, x, k]) => match natCast? k with
    | none
    | some 0 => pure ∅
    | some _ =>
      -- `k * x/k ≤ x < k * x/k + k`
      let ne_zero := mkApp3 (.const ``Ne [.succ .zero]) (.const ``Int []) k (toExpr (0 : Int))
      let pos := mkApp4 (.const ``LT.lt [.zero]) (.const ``Int []) (.const ``Int.instLTInt [])
        (toExpr (0 : Int)) k
      pure <|
      {mkApp3 (.const ``Int.mul_ediv_self_le []) x k (← mkDecideProof ne_zero),
        mkApp3 (.const ``Int.lt_mul_ediv_self_add []) x k (← mkDecideProof pos)}
  | _ => pure ∅

/--
Look up an expression in the atoms, recording it if it has not previously appeared.

Return its index, and, if it is new, a collection of interesting facts about the atom.
* for each new atom `a` of the form `((x : Nat) : Int)`, the fact that `0 ≤ a`
* for each new atom `a` of the form `x / k`, for `k` a positive numeral, the facts that
  `k * a ≤ x < k * a + k`
* for each new atom of the form `((a - b : Nat) : Int)`, the fact:
  `b ≤ a ∧ ((a - b : Nat) : Int) = a - b ∨ a < b ∧ ((a - b : Nat) : Int) = 0`
-/
def lookup (e : Expr) : OmegaM (Nat × Option (HashSet Expr)) := do
  let c ← getThe State
  for h : i in [:c.atoms.size] do
    have : i < c.atoms.size := h.2
    if ← isDefEq e c.atoms[i] then
      return (i, none)
  trace[omega] "New atom: {e}"
  let facts ← analyzeAtom e
  if ← isTracingEnabledFor `omega then
    unless facts.isEmpty do
      trace[omega] "New facts: {← facts.toList.mapM fun e => inferType e}"
  let i ← modifyGetThe State fun c => (c.atoms.size, { c with atoms := c.atoms.push e })
  return (i, some facts)

end Omega

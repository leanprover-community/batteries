/-
Copyright (c) 2021 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Std.Linter
import Std.Tactic.NoMatch
import Std.Tactic.GuardExpr
import Std.Tactic.ByCases
import Std.Tactic.SeqFocus
import Std.Tactic.ShowTerm
import Std.Tactic.SimpTrace
import Lean.Elab.Tactic.ElabTerm
import Std.Lean.Meta.Basic
import Std.Lean.Tactic

namespace Std.Tactic
open Lean Parser.Tactic Elab Command Elab.Tactic Meta

/-- `exfalso` converts a goal `⊢ tgt` into `⊢ False` by applying `False.elim`. -/
macro "exfalso" : tactic => `(tactic| apply False.elim)

/--
`_` in tactic position acts like the `done` tactic: it fails and gives the list
of goals if there are any. It is useful as a placeholder after starting a tactic block
such as `by _` to make it syntactically correct and show the current goal.
-/
macro "_" : tactic => `(tactic| {})

@[inherit_doc failIfSuccess]
syntax (name := failIfSuccessConv) "fail_if_success " Conv.convSeq : conv

attribute [tactic failIfSuccessConv] evalFailIfSuccess

/-- We allow the `rfl` tactic to also use `Iff.rfl`. -/
-- `rfl` was defined earlier in Lean4, at src/Lean/Init/Tactics.lean
-- Later we want to allow `rfl` to use all relations marked with an attribute.
macro_rules | `(tactic| rfl) => `(tactic| exact Iff.rfl)

macro_rules | `(tactic| rfl) => `(tactic| exact HEq.rfl)

/-- `rwa` calls `rw`, then closes any remaining goals using `assumption`. -/
macro "rwa " rws:rwRuleSeq loc:(location)? : tactic =>
  `(tactic| (rw $rws:rwRuleSeq $[$loc:location]?; assumption))

/--
Like `exact`, but takes a list of terms and checks that all goals are discharged after the tactic.
-/
elab (name := exacts) "exacts " "[" hs:term,* "]" : tactic => do
  for stx in hs.getElems do
    evalTactic (← `(tactic| exact $stx))
  evalTactic (← `(tactic| done))

/--
`by_contra h` proves `⊢ p` by contradiction,
introducing a hypothesis `h : ¬p` and proving `False`.
* If `p` is a negation `¬q`, `h : q` will be introduced instead of `¬¬q`.
* If `p` is decidable, it uses `Decidable.byContradiction` instead of `Classical.byContradiction`.
* If `h` is omitted, the introduced variable `_: ¬p` will be anonymous.
-/
macro (name := byContra) tk:"by_contra" e?:(ppSpace colGt binderIdent)? : tactic => do
  let e := match e? with
    | some e => match e with
      | `(binderIdent| $e:ident) => e
      | e => Unhygienic.run `(_%$e) -- HACK: hover fails without Unhygienic here
    | none => Unhygienic.run `(_%$tk)
  `(tactic| first
    | guard_target = Not _; intro $e:term
    | refine Decidable.byContradiction fun $e => ?_
    | refine Classical.byContradiction fun $e => ?_)

/--
Given a proof `h` of `p`, `absurd h` changes the goal to `⊢ ¬ p`.
If `p` is a negation `¬q` then the goal is changed to `⊢ q` instead.
-/
macro "absurd " h:term : tactic =>
  `(tactic| first | refine absurd ?_ $h | refine absurd $h ?_)

/--
`iterate n tac` runs `tac` exactly `n` times.
`iterate tac` runs `tac` repeatedly until failure.

To run multiple tactics, one can do `iterate (tac₁; tac₂; ⋯)` or
```lean
iterate
  tac₁
  tac₂
  ⋯
```
-/
syntax "iterate" (ppSpace num)? ppSpace tacticSeq : tactic
macro_rules
  | `(tactic| iterate $seq:tacticSeq) =>
    `(tactic| try ($seq:tacticSeq); iterate $seq:tacticSeq)
  | `(tactic| iterate $n $seq:tacticSeq) =>
    match n.1.toNat with
    | 0 => `(tactic| skip)
    | n+1 => `(tactic| ($seq:tacticSeq); iterate $(quote n) $seq:tacticSeq)

/--
`repeat' tac` runs `tac` on all of the goals to produce a new list of goals,
then runs `tac` again on all of those goals, and repeats until `tac` fails on all remaining goals.
-/
elab "repeat' " tac:tacticSeq : tactic => do
  setGoals (← repeat' (evalTacticAtRaw tac) (← getGoals))

/--
`repeat1' tac` applies `tac` to main goal at least once. If the application succeeds,
the tactic is applied recursively to the generated subgoals until it eventually fails.
-/
elab "repeat1' " tac:tacticSeq : tactic => do
  setGoals (← repeat1' (evalTacticAtRaw tac) (← getGoals))

/-- `subst_eqs` applies `subst` to all equalities in the context as long as it makes progress. -/
elab "subst_eqs" : tactic => Elab.Tactic.liftMetaTactic1 (·.substEqs)

/-- `split_ands` applies `And.intro` until it does not make progress. -/
syntax "split_ands" : tactic
macro_rules | `(tactic| split_ands) => `(tactic| repeat' refine And.intro ?_ ?_)

/--
`fapply e` is like `apply e` but it adds goals in the order they appear,
rather than putting the dependent goals first.
-/
elab "fapply " e:term : tactic =>
  evalApplyLikeTactic (·.apply (cfg := {newGoals := .all})) e

/--
`eapply e` is like `apply e` but it does not add subgoals for variables that appear
in the types of other goals. Note that this can lead to a failure where there are
no goals remaining but there are still metavariables in the term:
```
example (h : ∀ x : Nat, x = x → True) : True := by
  eapply h
  rfl
  -- no goals
-- (kernel) declaration has metavariables '_example'
```
-/
elab "eapply " e:term : tactic =>
  evalApplyLikeTactic (·.apply (cfg := {newGoals := .nonDependentOnly})) e

/--
Tries to solve the goal using a canonical proof of `True`, or the `rfl` tactic.
Unlike `trivial` or `trivial'`, does not use the `contradiction` tactic.
-/
macro (name := triv) "triv" : tactic =>
  `(tactic| first | exact trivial | rfl | fail "triv tactic failed")

/-- `conv` tactic to close a goal using an equality theorem. -/
macro (name := Conv.exact) "exact " t:term : conv => `(conv| tactic => exact $t)

/-- The `conv` tactic `equals` claims that the currently focused subexpression is equal
 to the given expression, and proves this claim using the given tactic.
```
example (P : (Nat → Nat) → Prop) : P (fun n => n - n) := by
  conv in (_ - _) => equals 0 =>
    -- current goal: ⊢ n - n = 0
    apply Nat.sub_self
  -- current goal: P (fun n => 0)
```
-/
macro (name := Conv.equals) "equals " t:term " => " tac:tacticSeq : conv =>
  `(conv| tactic => show (_ = $t); next => $tac)

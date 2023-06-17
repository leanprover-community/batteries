/-
Copyright (c) 2022 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Miyahara Kō
-/
import Lean.Meta.Tactic.Congr
import Std.Tactic.RCases
import Std.Tactic.Ext

/-! # `congr with` tactic, `rcongr` tactic -/

namespace Std.Tactic
open Lean Meta Elab Tactic Std.Tactic

/-- Configuration options for `congr` & `rcongr` -/
structure Congr.Config where
  /-- If `closePre := true`, it will attempt to close new goals using `Eq.refl`, `HEq.refl`, and
  `assumption` with reducible transparency. -/
  closePre : Bool := true
  /-- If `closePost := true`, it will try again on goals on which `congr` failed to make progress
  with default transparency. -/
  closePost : Bool := true

/-- Function elaborating `Congr.Config` -/
declare_config_elab Congr.elabConfig Congr.Config

@[inherit_doc Lean.Parser.Tactic.congr]
syntax (name := congrConfig) "congr" Parser.Tactic.config (ppSpace num)? : tactic

/--
Apply congruence (recursively) to goals of the form `⊢ f as = f bs` and `⊢ HEq (f as) (f bs)`.
* `congr n` controls the depth of the recursive applications.
  This is useful when `congr` is too aggressive in breaking down the goal.
  For example, given `⊢ f (g (x + y)) = f (g (y + x))`,
  `congr` produces the goals `⊢ x = y` and `⊢ y = x`,
  while `congr 2` produces the intended `⊢ x + y = y + x`.
* If, at any point, a subgoal matches a hypothesis then the subgoal will be closed.
* You can use `congr with p (: n)?` to call `ext p (: n)?` to all subgoals generated by `congr`.
  For example, if the goal is `⊢ f '' s = g '' s` then `congr with x` generates the goal
  `x : α ⊢ f x = g x`.
-/
syntax (name := congrWith) "congr" (ppSpace colGt num)?
  " with" (ppSpace colGt rintroPat)* (" : " num)? : tactic

@[inherit_doc Std.Tactic.congrWith]
syntax (name := congrConfigWith) "congr" Parser.Tactic.config (ppSpace colGt num)?
  " with" (ppSpace colGt rintroPat)* (" : " num)? : tactic

elab_rules : tactic
  | `(tactic| congr $cfg:config $[$n?]?) => do
    let config ← Congr.elabConfig (mkOptionalNode cfg)
    let hugeDepth := 1000000
    let depth := n?.map (·.getNat) |>.getD hugeDepth
    liftMetaTactic fun mvarId =>
      mvarId.congrN depth (closePre := config.closePre) (closePost := config.closePost)

macro_rules
  | `(tactic| congr $(depth)? with $ps* $[: $n]?) =>
    `(tactic| congr $(depth)? <;> ext $ps* $[: $n]?)
  | `(tactic| congr $config:config $(depth)? with $ps* $[: $n]?) =>
    `(tactic| congr $config:config $(depth)? <;> ext $ps* $[: $n]?)

/--
Recursive core of `rcongr`. Calls `ext pats <;> congr` and then itself recursively,
unless `ext pats <;> congr` made no progress.
-/
partial def rcongrCore (g : MVarId) (config : Congr.Config) (pats : List (TSyntax `rcasesPat))
    (acc : Array MVarId) : TermElabM (Array MVarId) := do
  let mut acc := acc
  for (g, qs) in (← Ext.extCore g pats (failIfUnchanged := false)).2 do
    let s ← saveState
    let gs ← g.congrN 1000000 (closePre := config.closePre) (closePost := config.closePost)
    if ← not <$> g.isAssigned <||> gs.anyM fun g' => return (← g'.getType).eqv (← g.getType) then
      s.restore
      acc := acc.push g
    else
      for g in gs do
        acc ← rcongrCore g config qs acc
  pure acc

/--
Repeatedly apply `congr` and `ext`, using the given patterns as arguments for `ext`.

There are two ways this tactic stops:
* `congr` fails (makes no progress), after having already applied `ext`.
* `congr` canceled out the last usage of `ext`. In this case, the state is reverted to before
  the `congr` was applied.

For example, when the goal is
```
⊢ (fun x => f x + 3) '' s = (fun x => g x + 3) '' s
```
then `rcongr x` produces the goal
```
x : α ⊢ f x = g x
```
This gives the same result as `congr; ext x; congr`.

In contrast, `congr` would produce
```
⊢ (fun x => f x + 3) = (fun x => g x + 3)
```
and `congr with x` (or `congr; ext x`) would produce
```
x : α ⊢ f x + 3 = g x + 3
```
-/
elab (name := rcongr) "rcongr" cfg:((Parser.Tactic.config)?) ps:(ppSpace colGt rintroPat)* :
    tactic => do
  let gs ← rcongrCore (← getMainGoal) (← Congr.elabConfig cfg)
    (RCases.expandRIntroPats ps).toList #[]
  replaceMainGoal gs.toList

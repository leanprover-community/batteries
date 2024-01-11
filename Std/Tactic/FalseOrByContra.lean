/-
Copyright (c) 2023 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Std.Lean.Expr
import Std.Lean.Meta.Basic

/-!
# `false_or_by_contra` tactic

Changes the goal to `False`, retaining as much information as possible:

If the goal is `False`, do nothing.
If the goal is an implication or a function type, introduce the argument.
(If the goal is `x ≠ y`, introduce `x = y`.)
Otherwise, for a goal `P`, replace it with `¬ ¬ P` and introduce `¬ P`.
-/

open Lean

/--
Changes the goal to `False`, retaining as much information as possible:

If the goal is `False`, do nothing.
If the goal is an implication or a function type, introduce the argument.
(If the goal is `x ≠ y`, introduce `x = y`.)
Otherwise, for a propositional goal `P`, replace it with `¬ ¬ P` and introduce `¬ P`.
For a non-propositional goal use `False.elim`.
-/
syntax (name := false_or_by_contra) "false_or_by_contra" : tactic

open Meta Elab Tactic

@[inherit_doc false_or_by_contra]
partial def falseOrByContra (g : MVarId) : MetaM MVarId := do
  let ty ← whnfR (← g.getType)
  match ty with
  | .const ``False _ => pure g
  | .forallE _ _ _ _
  | .app (.const ``Not _) _ => falseOrByContra (← g.intro1).2
  | _ =>
    if ← isProp ty then
      let [g] ← g.applyConst ``Classical.byContradiction | panic! "expected one sugoal"
      pure (← g.intro1).2
    else
      let [g] ← g.applyConst ``False.elim | panic! "expected one sugoal"
      pure g


@[inherit_doc falseOrByContra]
elab "false_or_by_contra" : tactic => liftMetaTactic1 (falseOrByContra ·)

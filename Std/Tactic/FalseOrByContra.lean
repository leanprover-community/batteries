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
If the goal is `¬ P`, introduce `P`.
If the goal is `x ≠ y`, introduce `x = y`.
Otherwise, for a goal `P`, replace it with `¬ ¬ P` and introduce `¬ P`.
-/

open Lean

/--
Changes the goal to `False`, retaining as much information as possible:

If the goal is `False`, do nothing.
If the goal is `¬ P`, introduce `P`.
If the goal is `x ≠ y`, introduce `x = y`.
Otherwise, for a goal `P`, replace it with `¬ ¬ P` and introduce `¬ P`.
-/
syntax (name := false_or_by_contra) "false_or_by_contra" : tactic

open Meta Elab Tactic

@[inherit_doc false_or_by_contra]
def falseOrByContra (g : MVarId) : MetaM (List MVarId) := do
  match ← whnfR (← g.getType) with
  | .const ``False _ => pure [g]
  | .app (.const ``Not _) _
  | .app (.const ``Ne _) _ => pure [(← g.intro1).2]
  | _ => (← g.applyConst ``Classical.byContradiction).mapM fun s => (·.2) <$> s.intro1

elab_rules : tactic
  | `(tactic| false_or_by_contra) => liftMetaTactic falseOrByContra

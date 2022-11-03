/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Mario Carneiro
-/
import Lean.Elab.ElabRules
import Std.Tactic.TryThis

namespace Std.Tactic
open Lean Elab Tactic TryThis

/--
`show_term tac` runs `tac`, then prints the generated term in the form
"exact X Y Z" or "refine X ?_ Z" if there are remaining subgoals.

(For some tactics, the printed term will not be human readable.)
-/
elab (name := showTermTac) tk:"show_term " t:tacticSeq : tactic => withMainContext do
  let g ← getMainGoal
  evalTactic t
  -- TODO: At the moment it is more useful to use an Expr MessageData
  -- instead of a Syntax because the former is clickable in the infoview
  -- addExactSuggestion tk (← instantiateMVars (mkMVar g)).headBeta
  logInfoAt tk (← instantiateMVars (mkMVar g)).headBeta

/--
`show_term e` elaborates `e`, then prints the generated term.

(For some tactics, the printed term will not be human readable.)
-/
elab (name := showTerm) tk:"show_term " t:term : term <= ty => do
  let e ← Term.elabTermEnsuringType t ty
  Term.synthesizeSyntheticMVarsNoPostponing
  -- TODO: At the moment it is more useful to use an Expr MessageData
  -- instead of a Syntax because the former is clickable in the infoview
  -- addTermSuggestion tk (← instantiateMVars e).headBeta
  logInfoAt tk (← instantiateMVars e).headBeta
  pure e

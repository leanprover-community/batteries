/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Mario Carneiro
-/
import Lean.Elab.ElabRules
import Lean.Meta.Tactic.TryThis

namespace Std.Tactic
open Lean Elab Tactic Meta.Tactic.TryThis

/--
`show_term tac` runs `tac`, then prints the generated term in the form
"exact X Y Z" or "refine X ?_ Z" if there are remaining subgoals.

(For some tactics, the printed term will not be human readable.)
-/
elab (name := showTermTac) tk:"show_term " t:tacticSeq : tactic => withMainContext do
  let g ← getMainGoal
  evalTactic t
  addExactSuggestion tk (← instantiateMVars (mkMVar g)).headBeta (origSpan? := ← getRef)

/-- Implementation of `show_term`. -/
local elab (name := showTermImpl) tk:"show_term_impl " t:term : term <= ty => do
  let e ← Term.elabTermEnsuringType t ty
  Term.synthesizeSyntheticMVarsNoPostponing
  addTermSuggestion tk (← instantiateMVars e).headBeta (origSpan? := ← getRef)
  pure e

/--
`show_term e` elaborates `e`, then prints the generated term.

(For some tactics, the printed term will not be human readable.)
-/
macro (name := showTerm) tk:"show_term " t:term : term =>
  `(no_implicit_lambda% (show_term_impl%$tk $t))

/--
The command `by?` will print a suggestion for replacing the proof block with a proof term
using `show_term`.
-/
macro (name := by?) tk:"by?" t:tacticSeq : term => `(show_term%$tk by%$tk $t)

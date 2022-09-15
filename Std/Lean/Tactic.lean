/-
Copyright (c) 2022 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Lean.Elab.Tactic.Basic

namespace Lean.Elab.Tactic

/--
Like `evalTacticAt`, but without restoring the goal list or pruning solved goals.
Useful when these tasks are already being done in an outer loop.
-/
def evalTacticAtRaw (tac : Syntax) (mvarId : MVarId) : TacticM (List MVarId) := do
  setGoals [mvarId]
  evalTactic tac
  getGoals

import Std.Data.MLList.IO
import Std.Data.MLList.Meta
import Std.Tactic.GuardMsgs
import Std.Tactic.RunCmd

set_option linter.missingDocs false

/-! ### Test fix to performance problem in `asArray`. -/

def g (n : Nat) : MLList Lean.Meta.MetaM Nat := do
  for _ in [:n] do
    if true then
      continue
  return n

/-- info: #[3000] -/
-- This used to fail before add the `uncons?` field to the implementation of `MLList`.
#guard_msgs in
#eval MLList.asArray $ (g 3000)

/-!
### Test `MLList.ofTaskList`.

We generate three tasks which sleep for `100`, `10`, and `1` milliseconds respectively,
and then verify that `MLList.ofTaskList` return their results in the order they complete.
-/

def sleep (n : UInt32) : BaseIO (Task UInt32) :=
  IO.asTask (do IO.sleep n; return n) |>.map fun t => t.map fun
  | .ok n => n
  | .error _ => 0

def sleeps : MLList BaseIO UInt32 := .squash fun _ => do
  let r ← [100,10,1].map sleep |>.traverse id
  return .ofTaskList r

/-- info: [1, 10, 100] -/
#guard_msgs in
#eval sleeps.force

/-!
### Test `runGreedily`

We verify that the monadic state at the completion of each job is available.

We run in parallel 5 jobs which create different numbers of subgoals.
We then sequentially count in each resulting state how many subgoals there are.
-/
open Lean Lean.Elab.Tactic Lean.Elab.Term

def job (n : Nat) : TacticM Unit := do
  evalTactic (← `(tactic| sleep $(quote (100*n)); iterate $(quote n) have : Nat := ?_))

def runGreedily : MLList TacticM Unit :=
  .squash fun _ => return (← TacticM.runGreedily ((List.range 5).map job)).2

def runGreedilyGoals := (runGreedily.mapM fun _ => return (← getGoals).length).force

/-- info: [1, 2, 3, 4, 5] -/
#guard_msgs in
example : True := by
  run_tac do logInfo s!"{← runGreedilyGoals}"
  -- It's nondeterministic which result we "end up in",
  -- although there should be at least one `Nat` subgoal.
  trivial
  exact 0
  all_goals exact 0

-- We check the examples from the doc-strings extracting the state after running greedily.
open Core Meta

example (jobs : List (CoreM α)) : MLList CoreM (α × Core.State) :=
  .squash fun _ => return (← CoreM.runGreedily jobs).2.mapM fun a => return (a, ← get)
example (jobs : List (MetaM α)) : MLList MetaM (α × Meta.State) :=
  .squash fun _ => return (← MetaM.runGreedily jobs).2.mapM fun a => return (a, ← get)
example (jobs : List (TermElabM α)) : MLList TermElabM (α × Elab.Term.State) :=
  .squash fun _ => return (← TermElabM.runGreedily jobs).2.mapM fun a => return (a, ← get)
example (jobs : List (TacticM α)) : MLList TacticM (α × Elab.Tactic.State) :=
  .squash fun _ => return (← TacticM.runGreedily jobs).2.mapM fun a => return (a, ← get)

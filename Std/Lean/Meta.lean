/-
Copyright (c) 2022 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Lean.MetavarContext
import Lean.Exception

namespace Lean.Meta

/--
`repeat' f` runs `f` on all of the goals to produce a new list of goals,
then runs `f` again on all of those goals, and repeats until `f` fails on all remaining goals,
or until `maxIters` total calls to `f` have occurred.
-/
def repeat' [Monad m] [MonadError m] [MonadMCtx m]
    (f : MVarId → m (List MVarId)) (gs : List MVarId) (maxIters := 100000) : m (List MVarId) := do
  let acc ← go maxIters gs [] #[]
  pure (← acc.filterM fun g => not <$> g.isAssigned).toList
where
  /-- Auxiliary for `repeat'`. `repeat'.go f maxIters gs stk acc` evaluates to
  essentially `acc.toList ++ repeat' f (gs::stk).join maxIters`: that is, `acc` are goals we will
  not revisit, and `(gs::stk).join` is the accumulated todo list of subgoals. -/
  go : Nat → List MVarId → List (List MVarId) → Array MVarId → m (Array MVarId)
  | _, [], [], acc => pure acc
  | n, [], gs::stk, acc => go n gs stk acc
  | n, g::gs, stk, acc => do
    if ← g.isAssigned then
      go n gs stk acc
    else
      match n with
      | 0 => pure (acc ++ gs)
      | n+1 =>
        match ← observing (f g) with
        | .ok gs' => go n gs' (gs::stk) acc
        | .error _ => go n gs stk (acc.push g)
termination_by _ n gs stk _ => (n, stk, gs)

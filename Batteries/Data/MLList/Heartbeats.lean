/-
Copyright (c) 2023 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Batteries.Data.MLList.Basic
import Lean.Util.Heartbeats

/-!
# Truncate a `MLList` when running out of available heartbeats.
-/

open Lean
open Lean.Core (CoreM)

/-- Take an initial segment of a monadic lazy list,
stopping when there is less than `percent` of the remaining allowed heartbeats.

If `getMaxHeartbeats` returns `0`, then this passes through the original list unmodified.

The `initial` heartbeat counter is recorded when the first element of the list is requested.
Then each time an element is requested from the wrapped list the heartbeat counter is checked, and
if `current * 100 / initial < percent` then that element is returned,
but no further elements.
-/
def MLList.whileAtLeastHeartbeatsPercent [Monad m] [MonadLiftT CoreM m]
    (L : MLList m α) (percent : Nat := 10) : MLList m α :=
  MLList.squash fun _ => do
    if (← getMaxHeartbeats) = 0 then do
      return L
    let initialHeartbeats ← getRemainingHeartbeats
    return L.takeUpToFirstM fun _ => do
      pure <| .up <| (← getRemainingHeartbeats) * 100 / initialHeartbeats < percent

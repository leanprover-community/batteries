/-
Copyright (c) 2023 Joachim Breitner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joachim Breitner
-/

import Std.Tactic.Basic


-- The example from the doc string

/-- warning: declaration uses 'sorry' -/
example (P : (Nat → Nat) → Prop) : P (fun n ↦ n - n) := by
  conv in (_ - _) => equals 0 =>
    -- current goal: ⊢ n - n = 0
    apply Nat.sub_self
  -- current goal: P (fun n => 0)
  sorry

-- This tests that the goal created by equals must be closed

/-- error: unsolved goals -/
example (P : (Nat → Nat) → Prop) : P (fun n ↦ n - n) := by
  conv in (_ - _) =>
    equals 0 => skip -- this should complain
    -- and at this point, there should be no goal left
    tactic => sorry
  sorry

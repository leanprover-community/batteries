/-
Copyright (c) 2022 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Batteries.Tactic.SeqFocus
public import Batteries.Tactic.Alias

@[expose] public section

namespace Std.Range

theorem size_stop_le_start : ∀ r : Range, r.stop ≤ r.start → r.size = 0
  | ⟨start, stop, step, _⟩, h => by
    simp_all [size]
    omega

theorem size_step_1 (start stop) : size ⟨start, stop, 1, by decide⟩ = stop - start := by
  simp [size]

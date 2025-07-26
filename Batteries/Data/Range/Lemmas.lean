/-
Copyright (c) 2022 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Batteries.Tactic.SeqFocus
import Batteries.Tactic.Alias

namespace Std.Range

@[deprecated size (since := "2024-12-19")] alias numElems := size

theorem size_stop_le_start : ∀ r : Range, r.stop ≤ r.start → r.size = 0
  | ⟨start, stop, step, _⟩, h => by
    simp_all [size, Nat.div_eq_zero_iff_lt]
    omega

@[deprecated size_stop_le_start (since := "2024-12-19")]
alias numElems_stop_le_start := size_stop_le_start

theorem size_step_1 (start stop) : size ⟨start, stop, 1, by decide⟩ = stop - start := by
  simp [size]

@[deprecated size_step_1 (since := "2024-12-19")]
alias numElems_step_1 := size_step_1

@[deprecated mem_of_mem_range' (since := "2024-12-19")]
alias mem_range'_elems := mem_of_mem_range'

@[deprecated forIn'_eq_forIn'_range' (since := "2024-12-19")]
alias forIn'_eq_forIn_range' := forIn'_eq_forIn'_range'

/-
Copyright (c) 2022 James Gallicchio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James Gallicchio
-/

import Std.Classes.Collections.Iterable

namespace Std.Range

instance : WFIterable Range Nat where
  ρ := Range
  toIterator r :=
    if r.step = 0 then ⟨0,0,1⟩ else r
  step := λ ⟨start, stop, step⟩ =>
    if start < stop
    then some (start, ⟨start+step, stop, step⟩)
    else none
  dom r := r.step > 0
  wf := invImage (fun r => r.stop + r.step - r.start) Nat.lt_wfRel
  h_toIterator r := by
    simp [Iterable.toIterator]
    split
    . simp
    . apply Nat.zero_lt_of_ne_zero
      assumption
  h_step r hr x r' h := by
    simp [InvImage, WellFoundedRelation.rel, Nat.lt_wfRel]
    simp [Iterable.step] at h
    split at h
    . next hstart =>
      cases r; case mk start stop step =>
      cases r'
      simp at h hr hstart ⊢
      match h with
      | ⟨h1, h2, h3, h4⟩ =>
      clear h; cases h1; cases h2; cases h3; cases h4
      rw [Nat.add_sub_add_right]
      refine ⟨?_, hr⟩
      apply Nat.lt_of_lt_of_le
      . have := Nat.add_lt_add_right hr (stop - x)
        simp at this
        exact this
      . rw [Nat.add_comm stop, Nat.add_sub_assoc]
        . apply Nat.le_refl
        . apply Nat.le_of_lt hstart
    . contradiction



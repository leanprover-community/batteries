/-
Copyright (c) 2022 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Batteries.Tactic.SeqFocus
import Batteries.Data.List.Lemmas

namespace Std.Range

/-- The number of elements contained in a `Std.Range`. -/
def numElems (r : Range) : Nat :=
  if r.step = 0 then
    -- This is a very weird choice, but it is chosen to coincide with the `forIn` impl
    if r.stop ≤ r.start then 0 else r.stop
  else
    (r.stop - r.start + r.step - 1) / r.step

theorem numElems_stop_le_start : ∀ r : Range, r.stop ≤ r.start → r.numElems = 0
  | ⟨start, stop, step⟩, h => by
    simp [numElems]; split <;> simp_all
    apply Nat.div_eq_of_lt; simp [Nat.sub_eq_zero_of_le h]
    exact Nat.pred_lt ‹_›

theorem numElems_step_1 (start stop) : numElems ⟨start, stop, 1⟩ = stop - start := by
  simp [numElems]

private theorem numElems_le_iff {start stop step i} (hstep : 0 < step) :
    (stop - start + step - 1) / step ≤ i ↔ stop ≤ start + step * i :=
  calc (stop - start + step - 1) / step ≤ i
    _ ↔ stop - start + step - 1 < step * i + step := by
      rw [← Nat.lt_succ (n := i), Nat.div_lt_iff_lt_mul hstep, Nat.mul_comm, ← Nat.mul_succ]
    _ ↔ stop - start + step - 1 < step * i + 1 + (step - 1) := by
      rw [Nat.add_right_comm, Nat.add_assoc, Nat.sub_add_cancel hstep]
    _ ↔ stop ≤ start + step * i := by
      rw [Nat.add_sub_assoc hstep, Nat.add_lt_add_iff_right, Nat.lt_succ,
        Nat.sub_le_iff_le_add']

theorem mem_range'_elems (r : Range) (h : x ∈ List.range' r.start r.numElems r.step) : x ∈ r := by
  obtain ⟨i, h', rfl⟩ := List.mem_range'.1 h
  refine ⟨Nat.le_add_right .., ?_⟩
  unfold numElems at h'; split at h'
  · split at h' <;> [cases h'; simp_all]
  · next step0 =>
    refine Nat.not_le.1 fun h =>
      Nat.not_le.2 h' <| (numElems_le_iff (Nat.pos_of_ne_zero step0)).2 h

theorem forIn'_eq_forIn_range' [Monad m] (r : Std.Range)
    (init : β) (f : (a : Nat) → a ∈ r → β → m (ForInStep β)) :
    forIn' r init f =
    forIn
      ((List.range' r.start r.numElems r.step).pmap Subtype.mk fun _ => mem_range'_elems r)
      init (fun ⟨a, h⟩ => f a h) := by
  let ⟨start, stop, step⟩ := r
  let L := List.range' start (numElems ⟨start, stop, step⟩) step
  let f' : { a // start ≤ a ∧ a < stop } → _ := fun ⟨a, h⟩ => f a h
  suffices ∀ H, forIn' [start:stop:step] init f = forIn (L.pmap Subtype.mk H) init f' from this _
  intro H; dsimp only [forIn', Range.forIn']
  if h : start < stop then
    simp [numElems, Nat.not_le.2 h, L]; split
    · subst step
      suffices ∀ n H init,
          forIn'.loop start stop 0 f n start (Nat.le_refl _) init =
          forIn ((List.range' start n 0).pmap Subtype.mk H) init f' from this _ ..
      intro n; induction n with (intro H init; unfold forIn'.loop; simp [*])
      | succ n ih => simp [ih (List.forall_mem_cons.1 H).2]; rfl
    · next step0 =>
      have hstep := Nat.pos_of_ne_zero step0
      suffices ∀ fuel l i hle H, l ≤ fuel →
          (∀ j, stop ≤ i + step * j ↔ l ≤ j) → ∀ init,
          forIn'.loop start stop step f fuel i hle init =
          List.forIn ((List.range' i l step).pmap Subtype.mk H) init f' by
        refine this _ _ _ _ _
          ((numElems_le_iff hstep).2 (Nat.le_trans ?_ (Nat.le_add_left ..)))
          (fun _ => (numElems_le_iff hstep).symm) _
        conv => lhs; rw [← Nat.one_mul stop]
        exact Nat.mul_le_mul_right stop hstep
      intro fuel; induction fuel with intro l i hle H h1 h2 init
      | zero => simp [forIn'.loop, Nat.le_zero.1 h1]
      | succ fuel ih =>
        cases l with
        | zero => rw [forIn'.loop]; simp [Nat.not_lt.2 <| by simpa using (h2 0).2 (Nat.le_refl _)]
        | succ l =>
          have ih := ih _ _ (Nat.le_trans hle (Nat.le_add_right ..))
            (List.forall_mem_cons.1 H).2 (Nat.le_of_succ_le_succ h1) fun i => by
              rw [Nat.add_right_comm, Nat.add_assoc, ← Nat.mul_succ, h2, Nat.succ_le_succ_iff]
          have := h2 0; simp at this
          rw [forIn'.loop]; simp [List.forIn, this, ih]; rfl
  else
    simp [List.range', h, numElems_stop_le_start ⟨start, stop, step⟩ (Nat.not_lt.1 h), L]
    cases stop <;> unfold forIn'.loop <;> simp [List.forIn', h]

theorem forIn_eq_forIn_range' [Monad m] (r : Std.Range)
    (init : β) (f : Nat → β → m (ForInStep β)) :
    forIn r init f = forIn (List.range' r.start r.numElems r.step) init f := by
  refine Eq.trans ?_ <| (forIn'_eq_forIn_range' r init (fun x _ => f x)).trans ?_
  · simp [forIn, forIn', Range.forIn, Range.forIn']
    suffices ∀ fuel i hl b, forIn'.loop r.start r.stop r.step (fun x _ => f x) fuel i hl b =
        forIn.loop f fuel i r.stop r.step b from (this _ ..).symm
    intro fuel; induction fuel <;> intro i hl b <;>
      unfold forIn.loop forIn'.loop <;> simp [*]
    split
    · simp [if_neg (Nat.not_le.2 ‹_›)]
    · simp [if_pos (Nat.not_lt.1 ‹_›)]
  · suffices ∀ L H, forIn (List.pmap Subtype.mk L H) init (f ·.1) = forIn L init f from this _ ..
    intro L; induction L generalizing init <;> intro H <;> simp [*]

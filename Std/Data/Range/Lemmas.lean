import Std.Tactic.ByCases
import Std.Data.List.Basic
import Std.Data.Nat.Lemmas

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

theorem forIn_eq_forIn_range' [Monad m] (r : Std.Range)
    (init : β) (f : Nat → β → m (ForInStep β)) :
    forIn r init f = forIn (List.range' r.start r.numElems r.step) init f := by
  let ⟨start, stop, step⟩ := r
  simp [forIn, Range.forIn]
  if h : stop ≤ start then
    simp [h, numElems_stop_le_start ⟨start, stop, step⟩ h]
    cases stop <;> simp [forIn.loop, List.forIn, h]
  else
    simp [numElems, h]; split
    · subst step
      suffices ∀ n, forIn.loop f n start stop 0 init = List.forIn (List.range' start n 0) init f by
        apply this
      intro n; induction n generalizing init <;> simp [forIn.loop, List.forIn, *]; rfl
    · next step0 =>
      have hstep := Nat.pos_of_ne_zero step0
      suffices ∀ l n, l ≤ n → (∀ i, stop ≤ start + i * step ↔ l ≤ i) →
          forIn.loop f n start stop step init =
          List.forIn (List.range' start l step) init f by
        have H (i : Nat) := calc stop ≤ start + i * step
          _ ↔ stop - start + step - 1 < i * step + 1 + (step - 1) := by
            rw [Nat.add_sub_assoc hstep, Nat.add_lt_add_iff_lt_right, Nat.lt_succ,
              Nat.sub_le_iff_le_add']
          _ ↔ stop - start + step - 1 < i * step + step := by
            rw [Nat.add_right_comm, Nat.add_assoc, Nat.sub_add_cancel hstep]
          _ ↔ (stop - start + step - 1) / step ≤ i := by
            rw [← Nat.lt_succ (n := i), Nat.div_lt_iff_lt_mul hstep, Nat.succ_mul]
        refine this _ _ ((H _).1 (Nat.le_trans ?_ (Nat.le_add_left ..))) H
        conv => lhs; rw [← Nat.mul_one stop]
        exact Nat.mul_le_mul_left stop hstep
      clear h; intro l n h1 h2; induction n generalizing l start init with
      | zero => simp [forIn.loop, Nat.le_zero.1 h1, List.forIn]
      | succ n ih =>
        cases l with
        | zero =>
          have := (h2 0).2 (Nat.le_refl _); simp at this
          simp [this, forIn.loop, List.forIn]
        | succ l =>
          have ih := fun b => ih b (start + step) l (Nat.le_of_succ_le_succ h1) fun i => by
            rw [Nat.add_right_comm, Nat.add_assoc, ← Nat.succ_mul, h2, Nat.succ_le_succ_iff]
          have := h2 0; simp [-Nat.not_le] at this
          simp [forIn.loop, List.forIn, this, ih]; rfl

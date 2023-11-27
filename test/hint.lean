import Std.Tactic.Hint
import Std.Tactic.GuardMsgs
import Std.Tactic.RunCmd
import Std.Data.Int.Lemmas

/-! # Tests for the `hint` framework. -/

-- I'm not sure if we should set up some basic `hint` tactics in Std, or not be at all opinionated.

register_hint split
register_hint intro
register_hint simp_all?
register_hint decide

/-
info: Try these:
• simp_all only [forall_true_left, p]
-/
#guard_msgs (drop info) in
example {P Q : Prop} (p : P) (f : P → Q) : Q := by hint

/--
info: Try these:
• simp_all only [and_self]
-/
#guard_msgs in
example {P Q R: Prop} (x : P ∧ Q ∧ R ∧ R) : Q ∧ P ∧ R := by hint

/--
info: Try these:
• decide
-/
#guard_msgs in
example : 37^2 - 35^2 = 72 * 2 := by hint

/--
info: Try these:
• simp_all only [Nat.zero_le, and_true]
---
warning: declaration uses 'sorry'
-/
#guard_msgs in
example {P : Nat → Prop} (_ : { x // P x }) : ∃ x, P x ∧ 0 ≤ x := by hint

/--
info: Try these:
• split
---
error: unsolved goals
case inr
P : Prop
inst✝ : Decidable P
h✝ : ¬P
⊢ False
-/
#guard_msgs in
example {P : Prop} [Decidable P] : if P then True else False := by hint

/-!
We now register a hint tactic that simulates a long running tactic,
in order to test that the `hint` tactic cancels long running tactics if another tactic successfully
closes the goal.

Note that while the tactic framework internally calls `IO.checkCanceled`,
calculations in the kernel do not, and so it is posssible that the cancellation request will fail.

I don't see a good way to verify this in the test file,
but you can check that in the final example below CPU usage drops to zero after `hint` returns.
Disabling the `cancel` step in the implementation of the `hint` tactic results in a processs
that continues using a CPU for 10 seconds after `hint` returns.
-/

/-- Busy wait for `millis` milliseconds, checking `checkCanceled`. -/
def busy_wait (millis : Nat) : IO Bool := do
  let start ← IO.monoMsNow
  while !(← IO.checkCanceled) && (← IO.monoMsNow) < start + millis do pure ()
  IO.checkCanceled

register_hint run_tac busy_wait 10000

/--
info: Try these:
• decide
-/
#guard_msgs in
example : True := by hint

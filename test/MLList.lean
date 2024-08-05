import Batteries.Data.MLList.IO
import Batteries.Data.List.Basic

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

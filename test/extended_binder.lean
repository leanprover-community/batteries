import Std.Util.ExtendedBinder
import Std.Tactic.GuardMsgs

namespace Testing

example (x : Nat) : (satisfies_binder_pred% x > 1) = (x > 1) := rfl
example (x : Nat) : (satisfies_binder_pred% x ≥ 1) = (x ≥ 1) := rfl
example (x : Nat) : (satisfies_binder_pred% x < 1) = (x < 1) := rfl
example (x : Nat) : (satisfies_binder_pred% x ≤ 1) = (x ≤ 1) := rfl

example : ∃ x < 5, x < 5 := ⟨0, by simp⟩

open Lean Elab Std.ExtendedBinder in
/-- Test function for getBinderPredOfProp -/
def runGetBinderPredOfProp (t : Term) : TermElabM Unit := do
  let res? ← liftMacroM <| getBinderPredOfProp t
  if let some (x, bp) := res? then
    logInfo m!"yes: {x},{bp}"
  else
    logInfo m!"no"

/-- info: no -/
#guard_msgs in #eval do runGetBinderPredOfProp (← `(x + 2))
/-- info: yes: x✝, > 2 -/
#guard_msgs in #eval do runGetBinderPredOfProp (← `(x > 2))
/-- info: yes: x✝, ≥ 2 -/
#guard_msgs in #eval do runGetBinderPredOfProp (← `(x ≥ 2))
/-- info: yes: x✝, < 2 -/
#guard_msgs in #eval do runGetBinderPredOfProp (← `(x < 2))
/-- info: yes: x✝, ≤ 2 -/
#guard_msgs in #eval do runGetBinderPredOfProp (← `(x ≤ 2))

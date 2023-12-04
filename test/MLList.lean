import Std.Data.MLList.Basic
import Std.Tactic.GuardMsgs

set_option linter.missingDocs false

def g (n : Nat) : MLList Lean.Meta.MetaM Nat := do
  for _ in [:n] do
    if true then
      continue
  return n

/-- info: #[3000] -/
-- This used to fail before add the `uncons?` field to the implementation of `MLList`.
#guard_msgs in
#eval MLList.asArray $ (g 3000)

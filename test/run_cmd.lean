import Lean.Elab.Tactic.ElabTerm
import Std.Tactic.GuardMsgs

open Lean Elab Tactic

/-- info: hello world -/
#guard_msgs in
run_cmd logInfo m!"hello world"

example : True := by
  run_tac
    evalApplyLikeTactic MVarId.apply (← `(True.intro))

example : True := by_elab
  Term.elabTerm (← `(True.intro)) none

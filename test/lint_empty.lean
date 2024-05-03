import Batteries
import Lean.Elab

set_option linter.all true

/-- Some syntax to elaborate in a fresh env -/
def natDef : String :=
"prelude

inductive Nat where
  | zero
  | succ (n : Nat) : Nat

def id (x : α) := x
"

open Lean Parser Elab in
/--
Test that the linters imported from Batteries all work when run on a declaration in an empty environment.

This runs the linters because there's a global IO.Ref that contains them, rather than having them
be in a field of the environment itself, precisely so they can run in situations like this. However,
a linter that assumes it's run in an environment with the Lean prelude available may use of things
like `find!` and `get!` in linters, with the result that the linter panics.

This test elaborates the definition of the natural numbers and the identity function in a fresh
environment with all linters enabled. Running the tests in an environment with `LEAN_ABORT_ON_PANIC`
set ensures that the linters can at least run.
-/
elab "#testInEmptyEnv" : command => do
  let context := mkInputContext natDef "test"
  let (header, state, msgs) ← parseHeader context
  let opts := Options.empty |>.setBool `linter.all true
  let (env, msgs) ← processHeader header opts msgs context
  if msgs.hasErrors then
    for msg in msgs.toList do logMessage msg
    liftM (m := IO) <| throw <| IO.userError "Errors in header"
  let cmdState := Command.mkState env msgs
  let s ← IO.processCommands context state cmdState
  for t in s.commandState.infoState.trees do
    pushInfoTree t
  for msg in s.commandState.messages.toList do
    logMessage msg

#testInEmptyEnv

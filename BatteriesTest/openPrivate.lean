import Batteries.Tactic.OpenPrivate

import BatteriesTest.OpenPrivateDefs



/-- error: Unknown identifier `secretNumber` -/
#guard_msgs in
#eval secretNumber


-- It works with one space between the tokens
/-- info: 2 -/
#guard_msgs in
open private secretNumber from BatteriesTest.OpenPrivateDefs in
#eval secretNumber


-- It also works with other kinds of whitespace between the tokens

/-- info: 2 -/
#guard_msgs in
open      private secretNumber from BatteriesTest.OpenPrivateDefs in
#eval secretNumber


/-- info: 2 -/
#guard_msgs in
open
  private secretNumber from BatteriesTest.OpenPrivateDefs in
#eval secretNumber

/-- info: 2 -/
#guard_msgs in
open /- Being sneaky! -/ private secretNumber from BatteriesTest.OpenPrivateDefs in
#eval secretNumber

/--
info: @[defeq] private theorem secretNumber.eq_def : secretNumber✝ = 2 :=
Eq.refl secretNumber✝
-/
#guard_msgs in
open private secretNumber.eq_def from BatteriesTest.OpenPrivateDefs in
#print secretNumber.eq_def

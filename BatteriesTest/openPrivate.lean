
import Batteries.Tactic.OpenPrivate

import BatteriesTest.OpenPrivateDefs



/-- error: unknown identifier 'secretNumber' -/
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

import Std.Tactic.Lemma
import Std.Tactic.GuardMsgs

-- lemma disabled by default
/--
info: Try this: theorem
---
error: `lemma` is not supported, please use `theorem` instead.
Use `set_option lang.lemmaCmd true` to enable the use of the `lemma` command
-/
#guard_msgs in
lemma test1 : 3 < 7 := by decide

-- lemma enabled for one command
set_option lang.lemmaCmd true in
lemma test2 : 3 < 7 := by decide

-- lemma disabled again
/--
info: Try this: theorem
---
error: `lemma` is not supported, please use `theorem` instead.
Use `set_option lang.lemmaCmd true` to enable the use of the `lemma` command
-/
#guard_msgs in
lemma test3 : 3 < 7 := by decide

-- lemma enabled for rest of file
set_option lang.lemmaCmd true

lemma test4 : 3 < 7 := by decide

lemma test5 : 3 < 7 := by decide

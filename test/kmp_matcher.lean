import Std.Tactic.GuardMsgs
import Std.Data.String.Basic

/-! Tests for Knuth-Morris-Pratt matching algorithm -/

/-- Matcher for pattern "abba" -/
def m := String.Matcher.ofString "abba"

/-- info: false -/
#guard_msgs in
#eval Option.isSome <| m.find? "AbbabbA" -- false

/-- info: true -/
#guard_msgs in
#eval Option.isSome <| m.find? "aabbaa" -- true

/-- info: 2 -/
#guard_msgs in
#eval Array.size <| m.findAll "abbabba" -- 2

/-- info: 3 -/
#guard_msgs in
#eval Array.size <| m.findAll "abbabbabba" -- 3

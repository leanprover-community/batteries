import Std.Tactic.GuardMsgs
import Std.Data.String.Basic

/-! Tests for Knuth-Morris-Pratt matching algorithm -/

/-- Matcher for pattern "abba" -/
def m := String.Matcher.ofString "abba"

#guard Option.isSome (m.find? "AbbabbA") = false

#guard Option.isSome (m.find? "aabbaa") = true

#guard Array.size (m.findAll "abbabba") = 2

#guard Array.size (m.findAll "abbabbabba") = 3

#guard Option.isSome ("xyyxx".findSubstr? "xy") = true

#guard Option.isSome ("xyyxx".findSubstr? "xyx") = false

#guard Array.size ("xyyxx".findAllSubstr "xyx") = 0

#guard Array.size ("xyyxxyx".findAllSubstr "xyx") = 1

#guard Array.size ("xyxyyxxyx".findAllSubstr "xyx") = 2

#guard Array.size ("xyxyxyyxxyxyx".findAllSubstr "xyx") = 4

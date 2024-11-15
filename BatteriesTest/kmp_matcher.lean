import Batteries.Data.String.Matcher

/-! Tests for Knuth-Morris-Pratt matching algorithm -/

/-- Matcher for pattern "abba" -/
def m := String.Matcher.ofString "abba"

#guard ! Option.isSome (m.find? "AbbabbA")

#guard Option.isSome (m.find? "aabbaa")

#guard Array.size (m.findAll "abbabba") = 2

#guard Array.size (m.findAll "abbabbabba") = 3

#guard Option.isSome ("xyyxx".findSubstr? "xy")

#guard ! Option.isSome ("xyyxx".findSubstr? "xyx")

#guard Array.size ("xyyxx".findAllSubstr "xyx") = 0

#guard Array.size ("xyyxxyx".findAllSubstr "xyx") = 1

#guard Array.size ("xyxyyxxyx".findAllSubstr "xyx") = 2

#guard Array.size ("xyxyxyyxxyxyx".findAllSubstr "xyx") = 4

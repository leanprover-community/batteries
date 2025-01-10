import Batteries.Data.String.Matcher
import Batteries.Data.List.Matcher

/-! # Tests for the Knuth-Morris-Pratt (KMP) matching algorithm -/

/-! ### String API -/

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

/-! ### List API -/

def lm := List.Matcher.ofList [0,1,1,0]

#guard lm.find? [2,1,1,0,1,1,2] == none

#guard lm.find? [0,0,1,1,0,0] == some (1, 5)

#guard (lm.findAll [0,1,1,0,1,1,0]).size == 2

#guard (lm.findAll [0,1,1,0,1,1,0,1,1,0]).size == 3

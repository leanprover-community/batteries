/-
Copyright (c) 2023 F. G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: F. G. Dorais
-/
import Batteries.Data.Array.Match
import Batteries.Data.String.Basic

namespace String

/-- Knuth-Morris-Pratt matcher type

This type is used to keep data for running the Knuth-Morris-Pratt (KMP) string matching algorithm.
KMP is a linear time algorithm to locate all substrings of a string that match a given pattern.
Generating the algorithm data is also linear in the length of the pattern but the data can be
re-used to match the same pattern over different strings.

The KMP data for a pattern string can be generated using `Matcher.ofString`. Then `Matcher.find?`
and `Matcher.findAll` can be used to run the algorithm on an input string.
```
def m := Matcher.ofString "abba"

#eval Option.isSome <| m.find? "AbbabbA" -- false
#eval Option.isSome <| m.find? "aabbaa" -- true

#eval Array.size <| m.findAll "abbabba" -- 2
#eval Array.size <| m.findAll "abbabbabba" -- 3
```
-/
structure Matcher extends Array.Matcher Char where
  /-- The pattern for the matcher -/
  pattern : Substring

/-- Make KMP matcher from pattern substring -/
@[inline] def Matcher.ofSubstring (pattern : Substring) : Matcher where
  toMatcher := Array.Matcher.ofStream pattern
  pattern := pattern

/-- Make KMP matcher from pattern string -/
@[inline] def Matcher.ofString (pattern : String) : Matcher :=
  Matcher.ofSubstring pattern

/-- The byte size of the string pattern for the matcher -/
abbrev Matcher.patternSize (m : Matcher) : Nat := m.pattern.bsize

/-- Find all substrings of `s` matching `m.pattern`. -/
partial def Matcher.findAll (m : Matcher) (s : Substring) : Array Substring :=
  loop s m.toMatcher #[]
where
  /-- Accumulator loop for `String.Matcher.findAll` -/
  loop (s : Substring) (am : Array.Matcher Char) (occs : Array Substring) : Array Substring :=
    match am.next? s with
    | none => occs
    | some (s, am) =>
      loop s am <| occs.push { s with
        startPos := ⟨s.startPos.byteIdx - m.patternSize⟩
        stopPos := s.startPos }

/-- Find the first substring of `s` matching `m.pattern`, or `none` if no such substring exists. -/
def Matcher.find? (m : Matcher) (s : Substring) : Option Substring :=
  match m.next? s with
  | none => none
  | some (s, _) =>
    some { s with
      startPos := ⟨s.startPos.byteIdx - m.patternSize⟩
      stopPos := s.startPos }

end String

namespace Substring

/--
Returns all the substrings of `s` that match `pattern`.
-/
@[inline] def findAllSubstr (s pattern : Substring) : Array Substring :=
  (String.Matcher.ofSubstring pattern).findAll s

/--
Returns the first substring of `s` that matches `pattern`,
or `none` if there is no such substring.
-/
@[inline] def findSubstr? (s pattern : Substring) : Option Substring :=
  (String.Matcher.ofSubstring pattern).find? s

/--
Returns true iff `pattern` occurs as a substring of `s`.
-/
@[inline] def containsSubstr (s pattern : Substring) : Bool :=
  s.findSubstr? pattern |>.isSome

end Substring

namespace String

@[inherit_doc Substring.findAllSubstr]
abbrev findAllSubstr (s : String) (pattern : Substring) : Array Substring :=
  (String.Matcher.ofSubstring pattern).findAll s

@[inherit_doc Substring.findSubstr?]
abbrev findSubstr? (s : String) (pattern : Substring) : Option Substring :=
  s.toSubstring.findSubstr? pattern

@[inherit_doc Substring.containsSubstr]
abbrev containsSubstr (s : String) (pattern : Substring) : Bool :=
  s.toSubstring.containsSubstr pattern

end String

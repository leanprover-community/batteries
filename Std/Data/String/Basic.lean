/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg, James Gallicchio, F. G. Dorais
-/

import Std.Data.Char
import Std.Data.Nat.Lemmas
import Std.Data.Array.Match

instance : Coe String Substring := ⟨String.toSubstring⟩

protected theorem String.Pos.ne_zero_of_lt : {a b : Pos} → a < b → b ≠ 0
| _, _, hlt, rfl => Nat.not_lt_zero _ hlt

namespace Substring

/--
Returns the longest common prefix of two substrings.
The returned substring will use the same underlying string as `s`.
-/
def commonPrefix (s t : Substring) : Substring :=
  { s with stopPos := loop s.startPos t.startPos }
where
  /-- Returns the ending position of the common prefix, working up from `spos, tpos`. -/
  loop spos tpos :=
    if h : spos < s.stopPos ∧ tpos < t.stopPos then
      if s.str.get spos == t.str.get tpos then
        have := Nat.sub_lt_sub_left h.1 (s.str.lt_next spos)
        loop (s.str.next spos) (t.str.next tpos)
      else
        spos
    else
      spos
termination_by loop => s.stopPos.byteIdx - spos.byteIdx

/--
Returns the longest common suffix of two substrings.
The returned substring will use the same underlying string as `s`.
-/
def commonSuffix (s t : Substring) : Substring :=
  { s with startPos := loop s.stopPos t.stopPos }
where
  /-- Returns the starting position of the common prefix, working down from `spos, tpos`. -/
  loop spos tpos :=
    if h : s.startPos < spos ∧ t.startPos < tpos then
      let spos' := s.str.prev spos
      let tpos' := t.str.prev tpos
      if s.str.get spos' == t.str.get tpos' then
        have : spos' < spos := s.str.prev_lt_of_pos spos (String.Pos.ne_zero_of_lt h.1)
        loop spos' tpos'
      else
        spos
    else
      spos
termination_by loop => spos.byteIdx

/--
If `pre` is a prefix of `s`, i.e. `s = pre ++ t`, returns the remainder `t`.
-/
def dropPrefix? (s : Substring) (pre : Substring) : Option Substring :=
  let t := s.commonPrefix pre
  if t.bsize = pre.bsize then
    some { s with startPos := t.stopPos }
  else
    none

/--
If `suff` is a suffix of `s`, i.e. `s = t ++ suff`, returns the remainder `t`.
-/
def dropSuffix? (s : Substring) (suff : Substring) : Option Substring :=
  let t := s.commonSuffix suff
  if t.bsize = suff.bsize then
    some { s with stopPos := t.startPos }
  else
    none

/-- The first position in `s.str` where `pattern` occurs,
    or `none` if no such position exists. -/
def posOfSubstr (s pattern : Substring) : Option String.Pos :=
  let m : Array.Matcher Char := .ofStream pattern
  match m.next? s with
  | none => none
  | some (s, _) => some ⟨s.startPos.byteIdx - pattern.bsize⟩

/-- Returns true iff `pattern` occurs as a substring of `s`. -/
def containsSubstr (s : Substring) (pattern : Substring) : Bool :=
  s.posOfSubstr pattern |>.isSome

end Substring

namespace String

/-- The first position at which `pattern` occurs in `s`, or `none` if it never occurs. -/
def posOfSubstr (s : String) (pattern : Substring) : Option String.Pos :=
  s.toSubstring.posOfSubstr pattern

/-- The first position at which `pattern` occurs in `s`, or `none` if it never occurs. -/
def posOfStr (s pattern : String) : Option String.Pos :=
  s.posOfSubstr pattern.toSubstring

/-- Returns true iff `pattern` occurs as a substring of `s`. -/
def containsSubstr (s : String) (pattern : Substring) : Bool :=
  s.posOfSubstr pattern |>.isSome

/-- Returns true iff `pattern` occurs as a substring of `s`. -/
def containsStr (s pattern : String) : Bool :=
  s.containsSubstr pattern.toSubstring

/--
If `pre` is a prefix of `s`, i.e. `s = pre ++ t`, returns the remainder `t`.
-/
def dropPrefix? (s : String) (pre : Substring) : Option Substring :=
  Substring.dropPrefix? s pre

/--
If `suff` is a suffix of `s`, i.e. `s = t ++ suff`, returns the remainder `t`.
-/
def dropSuffix? (s : String) (suff : Substring) : Option Substring :=
  Substring.dropSuffix? s suff

/-- `s.stripPrefix pre` will remove `pre` from the beginning of `s` if it occurs there,
or otherwise return `s`. -/
def stripPrefix (s : String) (pre : Substring) : String :=
  s.dropPrefix? pre |>.map Substring.toString |>.getD s

/-- `s.stripSuffix suff` will remove `suff` from the end of `s` if it occurs there,
or otherwise return `s`. -/
def stripSuffix (s : String) (suff : Substring) : String :=
  s.dropSuffix? suff |>.map Substring.toString |>.getD s

/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg, James Gallicchio
-/

import Std.Data.Char
import Std.Data.Nat.Lemmas

namespace Substring

/--
If `pre` is a prefix of `s`, i.e. `s = pre ++ t`, return the remainder `t`.
-/
def dropPrefix? (s : Substring) (pre : Substring) : Option Substring :=
  go 0 (pre.stopPos - pre.startPos)
where
  /-- Auxiliary definition for `dropPrefix?`. -/
  go (start : String.Pos) (stop : String.Pos) : Option Substring :=
    if h : start ≥ stop then
      some { s with startPos := s.startPos + start }
    else
      let cs := s.get start
      let cp := pre.get start
      if cs == cp then
        have : start.byteIdx + String.csize cs ≤ stop.byteIdx + 4 :=
          Nat.add_le_add (Nat.le_of_lt $ Nat.not_le.mp h) (String.csize_le_4 _)
        have : stop.byteIdx + 4 - (start.byteIdx + String.csize cs) <
                stop.byteIdx + 4 - start.byteIdx :=
          Nat.sub_add_lt_sub this (String.csize_pos _)
        go (start + cs) stop
      else
        none
termination_by go start stop => stop.byteIdx + 4 - start.byteIdx

/-- The first position in `s.str` where `pattern` occurs,
    or `none` if no such position exists. -/
def posOfSubstr (s pattern : Substring) : Option String.Pos :=
  if h : pattern.bsize > 0 then
    aux pattern.str pattern.startPos pattern.bsize h s.str s.stopPos s.startPos
  else some 0
where
  /-- Pattern string `ps` starting at `pstart` for `plen` bytes, looking for a
      match in string `s` starting after `start` and ending before `stop`. -/
  aux ps pstart plen (hplen : plen > 0) s (stop start : String.Pos) :=
    if h : start.byteIdx + plen ≤ stop.byteIdx then
      have : stop.byteIdx - (s.next start).byteIdx < stop.byteIdx - start.byteIdx :=
        Nat.sub_lt_sub_left
          (Nat.lt_of_lt_of_le (Nat.lt_add_of_pos_right hplen) h)
          (String.lt_next _ _)
      if String.substrEq s start pattern.str pattern.startPos pattern.bsize then
        some start
      else
        aux ps pstart plen hplen s stop (s.next start)
    else
      none
termination_by aux i => stop.byteIdx - i.byteIdx

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
If `pre` is a prefix of `s`, i.e. `s = pre ++ t`, return the remainder `t`.
-/
def dropPrefix? (s : String) (pre : String) : Option Substring :=
  s.toSubstring.dropPrefix? pre.toSubstring

/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Std.Data.Char
import Std.Data.Nat.Lemmas

namespace Substring

/-- Check if two substrings are equal as strings. -/
def eqAsString (s t : Substring) : Bool :=
  if s.bsize ≠ t.bsize then
    false
  else
    go s.bsize 0
where
  /-- Auxiliary definition for `eqAsString`. -/
  go (remaining : Nat) (offset : String.Pos) : Bool :=
    if h : remaining = 0 then
      true
    else
      let cs := s.get (s.startPos + offset)
      let ct := t.get (t.startPos + offset)
      if cs == ct then
        have : remaining - String.csize cs < remaining :=
          Nat.sub_lt (Nat.pos_of_ne_zero h) (String.csize_pos _)
        go (remaining - String.csize cs) (offset + cs)
      else
        false

/--
If `pre` is a prefix of `s`, i.e. `s = pre ++ t`, return the remainder `t`.
-/
def dropPrefix? (s : Substring) (pre : Substring) : Option Substring :=
  if s.bsize < pre.bsize then
    none
  else
    let p := s.startPos + (pre.stopPos - pre.startPos)
    if { s with stopPos := p }.eqAsString pre then
      some { s with startPos := p }
    else
      none

/--
If `suff` is a suffix of `s`, i.e. `s = t ++ suff`, return the remainder `t`.
-/
def dropSuffix? (s : Substring) (suff : Substring) : Option Substring :=
  if s.bsize < suff.bsize then
    none
  else
    let p := s.stopPos + (suff.stopPos - suff.startPos)
    if { s with startPos := p }.eqAsString suff then
      some { s with stopPos := p }
    else
      none

end Substring

namespace String

/--
If `pre` is a prefix of `s`, i.e. `s = pre ++ t`, return the remainder `t`.
-/
def dropPrefix? (s : String) (pre : String) : Option Substring :=
  s.toSubstring.dropPrefix? pre.toSubstring

/--
If `suff` is a suffix of `s`, i.e. `s = t ++ suff`, return the remainder `t`.
-/
def dropSuffix? (s : String) (suff : String) : Option Substring :=
  if s.endsWith suff then some <| s.toSubstring.dropRight suff.length else none

/-- `s.stripPrefix pre` will remove `pre` from the beginning of `s` if it occurs there,
or otherwise return `s`. -/
def stripPrefix (s pre : String) : String :=
  s.dropPrefix? pre |>.map Substring.toString |>.getD s

/-- `s.stripSuffix suff` will remove `suff` from the end of `s` if it occurs there,
or otherwise return `s`. -/
def stripSuffix (s suff : String) : String :=
  s.dropSuffix? suff |>.map Substring.toString |>.getD s

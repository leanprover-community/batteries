/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Std.Data.Char
import Std.Data.Nat.Lemmas

protected theorem String.Pos.ne_zero_of_lt : {a b : Pos} → a < b → b ≠ 0
| _, _, hlt, rfl => Nat.not_lt_zero _ hlt

namespace Substring

/-- Return the longest common prefix of two substrings. -/
def commonPrefix (s t : Substring) : Substring :=
  { s with stopPos := loop s.startPos t.startPos }
where
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

/-- Return the longest common suffix of two substrings. -/
def commonSuffix (s t : Substring) : Substring :=
  { s with startPos := loop s.stopPos t.stopPos }
where
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
If `pre` is a prefix of `s`, i.e. `s = pre ++ t`, return the remainder `t`.
-/
def dropPrefix? (s : Substring) (pre : Substring) : Option Substring :=
  let t := s.commonPrefix pre
  if t.bsize = pre.bsize then
    some { s with startPos := t.stopPos }
  else
    none

/--
If `suff` is a suffix of `s`, i.e. `s = t ++ suff`, return the remainder `t`.
-/
def dropSuffix? (s : Substring) (suff : Substring) : Option Substring :=
  let t := s.commonSuffix suff
  if t.bsize = suff.bsize then
    some { s with stopPos := t.startPos }
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

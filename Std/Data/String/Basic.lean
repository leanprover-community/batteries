/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
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

end Substring

namespace String

/--
If `pre` is a prefix of `s`, i.e. `s = pre ++ t`, return the remainder `t`.
-/
def dropPrefix? (s : String) (pre : String) : Option Substring :=
  s.toSubstring.dropPrefix? pre.toSubstring

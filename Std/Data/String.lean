/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

namespace String

/--
If `pre` is a prefix of `s`, i.e. `s = pre ++ t`, return the remainder `t`.
-/
def dropPrefix? (s : String) (pre : String) : Option Substring :=
  let s := s.toSubstring
  if s.take pre.length == pre.toSubstring then
    s.drop pre.length
  else
    none

end String

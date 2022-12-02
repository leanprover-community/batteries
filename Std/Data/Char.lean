/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Std.Tactic.RCases

namespace Char

private theorem csize_eq (c) :
    String.csize c = 1 ∨ String.csize c = 2 ∨ String.csize c = 3 ∨
    String.csize c = 4 := by
  simp only [String.csize, utf8Size]
  repeat (first | split | (solve | simp))

theorem csize_pos (c) : 0 < String.csize c := by
  rcases csize_eq c with _|_|_|_ <;> simp_all

theorem csize_le_4 (c) : String.csize c ≤ 4 := by
  rcases csize_eq c with _|_|_|_ <;> simp_all

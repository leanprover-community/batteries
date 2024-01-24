/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/
import Std.Tactic.Ext.Attr
import Std.Tactic.RCases

@[ext] theorem Char.ext : {a b : Char} → a.val = b.val → a = b
  | ⟨_,_⟩, ⟨_,_⟩, rfl => rfl

namespace String

private theorem csize_eq (c) :
    csize c = 1 ∨ csize c = 2 ∨ csize c = 3 ∨
    csize c = 4 := by
  simp only [csize, Char.utf8Size]
  repeat (first | split | (solve | simp (config := {decide := true})))

theorem csize_pos (c) : 0 < csize c := by
  rcases csize_eq c with _|_|_|_ <;> simp_all (config := {decide := true})

theorem csize_le_4 (c) : csize c ≤ 4 := by
  rcases csize_eq c with _|_|_|_ <;> simp_all (config := {decide := true})

end String

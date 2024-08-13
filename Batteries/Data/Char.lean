/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/
import Batteries.Data.UInt
import Batteries.Tactic.Alias

theorem Char.le_antisymm_iff {x y : Char} : x = y ↔ x ≤ y ∧ y ≤ x :=
  Char.ext_iff.trans UInt32.le_antisymm_iff

theorem Char.le_antisymm {x y : Char} (h1 : x ≤ y) (h2 : y ≤ x) : x = y :=
  Char.le_antisymm_iff.2 ⟨h1, h2⟩

instance : Batteries.LawfulOrd Char := .compareOfLessAndEq
  (fun _ => Nat.lt_irrefl _) Nat.lt_trans Nat.not_lt Char.le_antisymm

namespace String

@[deprecated (since := "2024-06-11")] alias csize_pos := Char.utf8Size_pos
@[deprecated (since := "2024-06-11")] alias csize_le_4 := Char.utf8Size_le_four

end String

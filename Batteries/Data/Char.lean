/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/
import Batteries.Data.UInt
import Batteries.Tactic.Alias

theorem Char.le_antisymm_iff {x y : Char} : x = y ↔ x ≤ y ∧ y ≤ x :=
  Char.ext_iff.trans UInt32.le_antisymm_iff

instance : Std.LawfulOrd Char :=
  Std.LawfulCmp.compareOfLessAndEq_of_irrefl_of_trans_of_not_lt_of_antisymm
    (fun _ => Nat.lt_irrefl _) Nat.lt_trans Nat.not_lt Char.le_antisymm

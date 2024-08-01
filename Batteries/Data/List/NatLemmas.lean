/-
Copyright (c) 2024 Bulhwi Cha. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Bulhwi Cha
-/
import Batteries.Data.Nat.Lemmas

/-!
This file contains lemmas about lists that use lemmas about the natural numbers.
-/

namespace List

theorem append_left_eq_self {a b : List α} : a ++ b = b ↔ a = [] := by
  constructor <;> intro h
  · exact List.eq_nil_of_length_eq_zero (Nat.add_left_eq_self.mp (h ▸ List.length_append a b).symm)
  · simp [h]

theorem append_right_eq_self {a b : List α} : a ++ b = a ↔ b = [] := by
  constructor <;> intro h
  · exact List.eq_nil_of_length_eq_zero (Nat.add_right_eq_self.mp (h ▸ List.length_append a b).symm)
  · simp [h]

end List

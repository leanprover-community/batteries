/-
Copyright (c) 2023 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/

@[simp] theorem Fin.zero_eta : (⟨0, Nat.zero_lt_succ _⟩ : Fin (n + 1)) = 0 := rfl

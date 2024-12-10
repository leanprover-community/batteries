/-
Copyright (c) 2024 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: François G. Dorais
-/

namespace Batteries

/-- Panic with a specific default value `v`. -/
def panicWith (v : α) (msg : String) : α := @panic α ⟨v⟩ msg

@[simp] theorem panicWith_eq (v : α) (msg) : panicWith v msg = v := rfl

/-
Copyright (c) 2023 James Gallicchio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James Gallicchio
-/

/-- Alias for `Sum.inl`. -/
@[match_pattern] def Sum.left (x : α) : α ⊕ β := .inl x

/-- Alias for `Sum.inr`. -/
@[match_pattern] def Sum.right (x : β) : α ⊕ β := .inr x

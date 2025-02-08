/-
Copyright (c) 2025 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: François G. Dorais
-/

import Batteries.Logic.Basic
import Batteries.Logic.Function
import Batteries.Tactic.Trans

open Function in
/-- `Equiv α β` is the type of functions from `α → β` with a two-sided inverse. -/
structure Equiv (α β : Sort _) where
  /-- Forward function of equivalence. -/
  protected toFun : α → β
  /-- Inverse function of equivalence. -/
  protected invFun : β → α
  /-- Inverse function is a left inverse. -/
  protected left_inv : LeftInverse invFun toFun
  /-- Inverse function is a right inverse. -/
  protected right_inv : RightInverse invFun toFun

namespace Equiv

@[ext] theorem ext {e₁ e₂ : Equiv α β} (H : ∀ x, e₁.toFun x = e₂.toFun x) : e₁ = e₂ := by
  have hto : e₁.toFun = e₂.toFun := funext H
  have hinv : e₁.invFun = e₂.invFun := by
    funext x; conv => lhs; rw [← e₂.right_inv x, ← H, e₁.left_inv]
  cases e₁; cases e₂; congr

-- /-- Identity equivalence. -/
-- protected def id (α) : Equiv α α where
--   toFun := id
--   invFun := id
--   left_inv _ := rfl
--   right_inv _ := rfl

-- /-- Inverse of an equivalence. -/
-- protected def inv (e : Equiv α β) : Equiv β α where
--   toFun := e.invFun
--   invFun := e.toFun
--   left_inv := e.right_inv
--   right_inv := e.left_inv

-- /-- Composition of equivalences. -/
-- protected def comp (e₁ : Equiv β γ) (e₂ : Equiv α β) : Equiv α γ where
--   toFun := e₁.toFun ∘ e₂.toFun
--   invFun := e₂.invFun ∘ e₁.invFun
--   left_inv := e₁.left_inv.comp e₂.left_inv
--   right_inv := e₁.right_inv.comp e₂.right_inv

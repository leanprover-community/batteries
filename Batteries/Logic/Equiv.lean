/-
Copyright (c) 2025 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: François G. Dorais
-/

import Batteries.Logic.Basic
import Batteries.Logic.Function
import Batteries.Tactic.Trans

open Function

/-- `α ≃ β` is the type of functions from `α → β` with a two-sided inverse. -/
structure Equiv (α β : Sort _) where
  /-- Forward function of equivalence. -/
  protected toFun : α → β
  /-- Inverse function of equivalence. -/
  protected invFun : β → α
  /-- Inverse function is a left inverse. -/
  protected left_inv : LeftInverse invFun toFun
  /-- Inverse function is a right inverse. -/
  protected right_inv : RightInverse invFun toFun

@[inherit_doc]
infixl:25 " ≃ " => Equiv

namespace Equiv

@[ext] theorem ext {e₁ e₂ : Equiv α β} (H : ∀ x, e₁.toFun x = e₂.toFun x) : e₁ = e₂ := by
  have hto : e₁.toFun = e₂.toFun := by funext; exact H ..
  have hinv : e₁.invFun = e₂.invFun := by
    funext x; rw [← e₁.right_inv x, e₁.left_inv, H (e₁.invFun x), e₂.left_inv]
  cases e₁; cases e₂; congr

/-- Identity equivalence `α ≃ α`. -/
@[refl] protected def refl (α) : α ≃ α where
  toFun := id
  invFun := id
  left_inv _ := rfl
  right_inv _ := rfl

/-- Inverse of an equivalence `e : α ≃ β`. -/
@[symm] protected def symm (e : α ≃ β) : β ≃ α where
  toFun := e.invFun
  invFun := e.toFun
  left_inv := e.right_inv
  right_inv := e.left_inv

/-- Composition of equivalences `e₁ : α ≃ β` and `e₂ : β ≃ γ`. -/
@[trans] protected def trans (e₁ : α ≃ β) (e₂ : β ≃ γ) : α ≃ γ where
  toFun := e₂.toFun ∘ e₁.toFun
  invFun := e₁.invFun ∘ e₂.invFun
  left_inv := e₂.left_inv.comp e₁.left_inv
  right_inv := e₂.right_inv.comp e₁.right_inv

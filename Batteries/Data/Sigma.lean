/-
Copyright (c) 2024 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: François G. Dorais
-/

namespace Sigma

/-- Type value of a `Sigma` object. -/
protected abbrev type (a : Sigma α) : Type _ := α a.fst

/-- Casts an `Sigma` object to  a value of compatible type. -/
protected def cast : (a : Sigma α) → a.type = β → β
  | {snd := a}, rfl => a

/-- Casts an `Sigma` object to  a value of compatible index. -/
protected def castIdx : (a : Sigma α) → a.fst = i → α i
  | {snd := a}, rfl => a

@[simp]
theorem mk_val (a : Sigma α) : ⟨_, a.snd⟩ = a := rfl

@[simp]
theorem cast_heq_val : (a : Sigma α) → (h : a.type = β) → HEq (a.cast h) a.snd
  | {..}, rfl => .rfl

@[simp]
theorem castIdx_heq_val : (a : Sigma α) → (h : a.fst = i) → HEq (a.castIdx h) a.snd
  | {..}, rfl => .rfl

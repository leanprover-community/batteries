/-
Copyright (c) 2025 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: François G. Dorais
-/

namespace Function

/-! ## id -/

theorem id_def : @id α = fun x => x := rfl

@[simp] theorem id_apply : id x = x := rfl

@[simp] theorem id_comp : id ∘ f = f := funext fun _ => rfl

@[simp] theorem comp_id : f ∘ id = f := funext fun _ => rfl

/-! ## LeftInverse -/

/-- `LeftInverse g f` means that `g` is a left inverse to `f`. That is, `g ∘ f = id`. -/
def LeftInverse (g : β → α) (f : α → β) : Prop := ∀ x, g (f x) = x

theorem LeftInverse.comp (hf : LeftInverse f g) (hh : LeftInverse h i) :
    LeftInverse (h ∘ f) (g ∘ i) := fun a => show h (f (g (i a))) = a by rw [hf (i a), hh a]

/-! ## RightInverse -/

/-- `RightInverse g f` means that `g` is a right inverse to `f`. That is, `f ∘ g = id`. -/
def RightInverse (g : β → α) (f : α → β) : Prop := LeftInverse f g

theorem RightInverse.comp (hf : RightInverse f g) (hh : RightInverse h i) :
    RightInverse (h ∘ f) (g ∘ i) := LeftInverse.comp hh hf

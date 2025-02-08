/-
Copyright (c) 2025 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: François G. Dorais
-/

namespace Function

/-! ## id -/

theorem id_def : @id α = fun x => x := rfl

theorem id_apply : id x = x := rfl

theorem id_comp : id ∘ f = f := funext fun _ => rfl

theorem comp_id : f ∘ id = f := funext fun _ => rfl

/-! ## LeftInverse, RightInverse -/

/-- `LeftInverse g f` means that `g` is a left inverse to `f`. That is, `g ∘ f = id`. -/
def LeftInverse (g : β → α) (f : α → β) : Prop := ∀ x, g (f x) = x

protected theorem LeftInverse.id (h : LeftInverse g f) : g ∘ f = id := funext h

theorem LeftInverse.comp (hf : LeftInverse f g) (hh : LeftInverse h i) :
    LeftInverse (h ∘ f) (g ∘ i) := fun a => show h (f (g (i a))) = a by rw [hf (i a), hh a]

theorem leftInverse_iff_comp {f : α → β} {g : β → α} : LeftInverse f g ↔ f ∘ g = id :=
  ⟨LeftInverse.id, congrFun⟩

/-- `RightInverse g f` means that `g` is a right inverse to `f`. That is, `f ∘ g = id`. -/
def RightInverse (g : β → α) (f : α → β) : Prop := LeftInverse f g

protected theorem RightInverse.id (h : RightInverse g f) : f ∘ g = id := funext h

theorem rightInverse_iff_comp {f : α → β} {g : β → α} : RightInverse f g ↔ g ∘ f = id :=
  ⟨RightInverse.id, congrFun⟩

theorem RightInverse.comp (hf : RightInverse f g) (hh : RightInverse h i) :
    RightInverse (h ∘ f) (g ∘ i) := LeftInverse.comp hh hf

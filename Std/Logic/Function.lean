/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad, Haitao Zhang, Yury Kudryashov
-/
import Std.Logic.Basic

/-!
# General operations on functions

In this file we define the following predicates on functions `f : α → β`:

- `Function.Injective`: `f x = f y` implies `x = y`;
- `Function.Surjective`: each `y` is equal to `f x` for some `x`;
- `Function.Bijective`: a function is both injective and bijective;
- `Function.Involutive`: `f (f x) = x` for all `x`.

We also prove some theorems about these definitions and functions in general.
-/

set_option autoImplicit false

universe u v w x

namespace Function

variable {α : Sort u} {β : Sort v} {γ : Sort w} {δ : Sort x} {f : α → β} {g : β → γ}

/-! ### Definitions and `*_def` theorems -/

/-- A function `f : α → β` is called injective if `f x = f y` implies `x = y`. -/
def Injective (f : α → β) : Prop := ∀ ⦃a₁ a₂⦄, f a₁ = f a₂ → a₁ = a₂

/-- A function `f : α → β` is called surjective if every `b : β` is equal to `f a`
for some `a : α`. -/
def Surjective (f : α → β) : Prop := ∀ b, ∃ a, f a = b

/-- A function is called bijective if it is both injective and surjective. -/
def Bijective (f : α → β) : Prop := Injective f ∧ Surjective f

/-- A function is involutive, if `f (f x) = x` for all `x`. -/
def Involutive (f : α → α) : Prop := ∀ x, f (f x) = x

theorem id_def : @id α = fun x => x := rfl
theorem flip_def {f : α → β → γ} : flip f = fun b a => f a b := rfl
theorem const_def {y : β} : (fun _ : α => y) = const α y := rfl

/-! ### Functional extensionality -/

theorem funext_iff {β : α → Sort v} {f g : (x : α) → β x} : f = g ↔ ∀ a, f a = g a :=
  ⟨congr_fun, funext⟩

theorem _root_.Classical.function_ne_iff {β : α → Sort v} {f g : (a : α) → β a} :
    f ≠ g ↔ ∃ a, f a ≠ g a :=
  (not_congr funext_iff).trans Classical.not_forall

/-- Heterogeneous version of `funext`. -/
theorem hfunext {α α' : Sort u} {β : α → Sort v} {β' : α' → Sort v} {f : (a : α) → β a}
    {g : (a : α') → β' a} (hα : α = α') (h : ∀ x y, HEq x y → HEq (f x) (g y)) : HEq f g := by
  subst hα
  have : ∀ a, HEq (f a) (g a) := fun a => h a a (HEq.refl a)
  have : β = β' := funext fun a => type_eq_of_heq (this a)
  subst this
  apply heq_of_eq
  funext a
  exact eq_of_heq (this a)

/-! ### Composition of functions -/

@[simp] theorem id_comp (f : α → β) : id ∘ f = f := rfl
@[simp] theorem comp_id (f : α → β) : f ∘ id = f := rfl

theorem comp_assoc (f : γ → δ) (g : β → γ) (h : α → β) : (f ∘ g) ∘ h = f ∘ g ∘ h := rfl

@[simp] theorem const_comp {c : γ} : const β c ∘ f = const α c := rfl
@[simp] theorem comp_const {b : β} : g ∘ const α b = const α (g b) := rfl

/-! ### Injective functions -/

theorem injective_id : Injective (@id α) := fun _a _b h => h

namespace Injective

variable {x y : α}

/-- Composition of injective functions in injective. -/
protected theorem comp (hg : Injective g) (hf : Injective f) : Injective (g ∘ f) := fun _ _ h =>
  hf (hg h)

theorem eq_iff (I : Injective f) : f x = f y ↔ x = y := ⟨@I _ _, congr_arg f⟩

theorem eq_iff' (I : Injective f) {z : β} (h : f y = z) : f x = z ↔ x = y := h ▸ I.eq_iff

theorem ne_iff (hf : Injective f) : f x ≠ f y ↔ x ≠ y := not_congr hf.eq_iff

alias ⟨_, ne⟩ := ne_iff

theorem ne_iff' (hf : Injective f) {z : β} (h : f y = z) : f x ≠ z ↔ x ≠ y := h ▸ hf.ne_iff

/-- If the co-domain `β` of an injective function `f : α → β` has decidable equality, then
the domain `α` also has decidable equality. -/
protected def decidableEq [DecidableEq β] (I : Injective f) : DecidableEq α := fun _ _ =>
  decidable_of_iff _ I.eq_iff

/-- If the composition `g ∘ f` is injective, then so is the right function `f`. -/
theorem of_comp (I : Injective (g ∘ f)) : Injective f := fun _ _ h => I <| congr_arg g h

@[simp] theorem comp_left_iff (hg : Injective g) : Injective (g ∘ f) ↔ Injective f :=
  ⟨Injective.of_comp, hg.comp⟩

/-- Composition by an injective function on the left is itself injective. -/
theorem comp_left (hg : Injective g) : Injective (g ∘ · : (α → β) → α → γ) := fun _ _ hgf =>
  funext fun i => hg <| congr_fun hgf i

protected theorem dite (p : α → Prop) [DecidablePred p]
    {f : {a : α // p a} → β} {f' : {a : α // ¬ p a} → β}
    (hf : Injective f) (hf' : Injective f')
    (im_disj : ∀ {x x' : α} {hx : p x} {hx' : ¬ p x'}, f ⟨x, hx⟩ ≠ f' ⟨x', hx'⟩) :
    Injective (fun x => if h : p x then f ⟨x, h⟩ else f' ⟨x, h⟩) := fun x₁ x₂ h => by
 dsimp only at h
 by_cases h₁ : p x₁ <;> by_cases h₂ : p x₂
 · rw [dif_pos h₁, dif_pos h₂] at h; injection (hf h)
 · rw [dif_pos h₁, dif_neg h₂] at h; exact (im_disj h).elim
 · rw [dif_neg h₁, dif_pos h₂] at h; exact (im_disj h.symm).elim
 · rw [dif_neg h₁, dif_neg h₂] at h; injection (hf' h)

end Injective

theorem const_injective [Nonempty α] : Injective (const α : β → α → β) := fun y₁ y₂ h =>
  let ⟨x⟩ := ‹Nonempty α›
  congr_fun h x

@[simp] theorem const_inj [Nonempty α] {y₁ y₂ : β} : const α y₁ = const α y₂ ↔ y₁ = y₂ :=
  const_injective.eq_iff

theorem injective_of_subsingleton [Subsingleton α] (f : α → β) : Injective f := fun _ _ _ =>
  Subsingleton.elim _ _

/-! ### Surjective functions -/

namespace Surjective

protected theorem comp (hg : Surjective g) (hf : Surjective f) : Surjective (g ∘ f) := fun c : γ =>
  let ⟨b, hb⟩ := hg c; let ⟨a, ha⟩ := hf b; ⟨a, (congr_arg g ha).trans hb⟩

theorem of_comp (S : Surjective (g ∘ f)) : Surjective g := fun y => let ⟨x, h⟩ := S y; ⟨f x, h⟩

@[simp] theorem comp_right_iff (hf : Surjective f) : Surjective (g ∘ f) ↔ Surjective g :=
  ⟨Surjective.of_comp, fun h => h.comp hf⟩

theorem of_comp_left (S : Surjective (g ∘ f)) (hg : Injective g) : Surjective f := fun a =>
  let ⟨c, hc⟩ := S (g a); ⟨c, hg hc⟩

protected theorem «forall» (hf : Surjective f) {p : β → Prop} : (∀ y, p y) ↔ ∀ x, p (f x) :=
  ⟨fun h x => h (f x), fun h y => let ⟨x, hx⟩ := hf y; hx ▸ h x⟩

protected theorem forall₂ (hf : Surjective f) {p : β → β → Prop} :
    (∀ y₁ y₂, p y₁ y₂) ↔ ∀ x₁ x₂, p (f x₁) (f x₂) :=
  hf.forall.trans <| forall_congr' fun _ => hf.forall

protected theorem forall₃ (hf : Surjective f) {p : β → β → β → Prop} :
    (∀ y₁ y₂ y₃, p y₁ y₂ y₃) ↔ ∀ x₁ x₂ x₃, p (f x₁) (f x₂) (f x₃) :=
  hf.forall.trans <| forall_congr' fun _ => hf.forall₂

protected theorem «exists» (hf : Surjective f) {p : β → Prop} :
    (∃ y, p y) ↔ ∃ x, p (f x) :=
  ⟨fun ⟨y, hy⟩ => let ⟨x, hx⟩ := hf y; ⟨x, hx.symm ▸ hy⟩, fun ⟨x, hx⟩ => ⟨f x, hx⟩⟩

protected theorem exists₂ (hf : Surjective f) {p : β → β → Prop} :
    (∃ y₁ y₂, p y₁ y₂) ↔ ∃ x₁ x₂, p (f x₁) (f x₂) :=
  hf.exists.trans <| exists_congr fun _ => hf.exists

protected theorem exists₃ (hf : Surjective f) {p : β → β → β → Prop} :
    (∃ y₁ y₂ y₃, p y₁ y₂ y₃) ↔ ∃ x₁ x₂ x₃, p (f x₁) (f x₂) (f x₃) :=
  hf.exists.trans <| exists_congr fun _ => hf.exists₂

end Surjective

theorem surjective_id : Surjective (@id α) := fun a => ⟨a, rfl⟩

/-!
### Bijective functions

This section contains theorems about bijective functions
and theorems that involve both injective and surjective functions.
-/

theorem bijective_id : Bijective (@id α) := ⟨injective_id, surjective_id⟩

namespace Bijective

protected theorem injective (hf : Bijective f) : Injective f := hf.1
protected theorem surjective (hf : Bijective f) : Surjective f := hf.2

protected theorem comp (hg : Bijective g) (hf : Bijective f) : Bijective (g ∘ f) :=
  ⟨hg.1.comp hf.1, hg.2.comp hf.2⟩

end Bijective

/-- If the composition of `f` with a surjective function is injective , then so is `f`. -/
theorem Injective.of_comp_right {g : γ → α} (I : Injective (f ∘ g)) (hg : Surjective g) :
    Injective f :=
  hg.forall₂.2 fun _ _ h => congr_arg g (I h)

@[simp]
theorem injective_comp_right_iff (hf : Bijective f) : Injective (g ∘ f) ↔ Injective g :=
  ⟨fun I => I.of_comp_right hf.surjective, fun h => h.comp hf.injective⟩

theorem Surjective.injective_comp_right (hf : Surjective f) : Injective fun g : β → γ => g ∘ f :=
  fun _ _ h => funext <| hf.forall.2 <| congr_fun h

protected theorem Surjective.right_cancellable (hf : Surjective f) {g₁ g₂ : β → γ} :
    g₁ ∘ f = g₂ ∘ f ↔ g₁ = g₂ :=
  hf.injective_comp_right.eq_iff

theorem surjective_of_right_cancellable_Prop (h : ∀ g₁ g₂ : β → Prop, g₁ ∘ f = g₂ ∘ f → g₁ = g₂) :
    Surjective f := by
  specialize h (fun y => ∃ x, f x = y) (fun _ => True) (funext fun x => eq_true ⟨_, rfl⟩)
  intro y; rw [congr_fun h y]; trivial

/-- If the composition of two surjective maps is injective, then both maps are bijective. -/
theorem Surjective.bijective₂_of_injective {g : γ → α} (hf : Surjective f) (hg : Surjective g)
    (I : Injective (f ∘ g)) : Bijective f ∧ Bijective g :=
  ⟨⟨I.of_comp_right hg, hf⟩, I.of_comp, hg⟩

/-- If the composition of two injective maps is surjective, then both maps are bijective. -/
theorem Injective.bijective₂_of_surjective {g : γ → α} (hf : Injective f) (hg : Injective g)
    (S : Surjective (f ∘ g)) : Bijective f ∧ Bijective g :=
  ⟨⟨hf, S.of_comp⟩, hg, S.of_comp_left hf⟩

@[simp]
theorem surjective_comp_left_iff (hf : Bijective f) {g : γ → α} :
    Surjective (f ∘ g) ↔ Surjective g :=
  ⟨fun S => S.of_comp_left hf.1, hf.surjective.comp⟩

theorem Bijective.of_comp_iff (hf : Bijective f) :
    Bijective (g ∘ f) ↔ Bijective g :=
  and_congr (injective_comp_right_iff hf) (hf.surjective.comp_right_iff)

theorem Bijective.of_comp_iff' {f : α → β} (hf : Bijective f) (g : γ → α) :
    Function.Bijective (f ∘ g) ↔ Function.Bijective g :=
  and_congr hf.injective.comp_left_iff (surjective_comp_left_iff hf)

namespace Involutive

theorem _root_.Bool.involutive_not : Involutive not := Bool.not_not

variable {f : α → α} (hf : Involutive f)

@[simp] theorem comp_self : f ∘ f = id := funext hf

protected theorem injective : Injective f := fun x y h =>
  hf x ▸ hf y ▸ congr_arg f h

protected theorem surjective : Surjective f := fun x => ⟨f x, hf x⟩

protected theorem bijective : Bijective f := ⟨hf.injective, hf.surjective⟩

/-- An involution commutes across an equality. Compare to `Function.Injective.eq_iff`. -/
protected theorem eq_iff {x y : α} : f x = y ↔ x = f y := hf.injective.eq_iff' (hf y)

end Involutive

end Function

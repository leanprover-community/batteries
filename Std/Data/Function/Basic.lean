/-
Copyright (c) Mathlib contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
import Std.Logic

namespace Function

theorem funext_iff {β : α → Sort _} {f₁ f₂ : ∀ x : α, β x} : f₁ = f₂ ↔ ∀ a, f₁ a = f₂ a :=
  Iff.intro (fun h _ ↦ h ▸ rfl) funext

section Update

variable {α : Sort u} {β : α → Sort v} {α' : Sort w} [DecidableEq α] [DecidableEq α']
  {f g : (a : α) → β a} {a : α} {b : β a}

/-- Replacing the value of a function at a given point by a given value. -/
def update (f : ∀ a, β a) (a' : α) (v : β a') (a : α) : β a :=
  if h : a = a' then Eq.ndrec v h.symm else f a

/-- On non-dependent functions, `Function.update` can be expressed as an `ite` -/
theorem update_apply {β : Sort _} (f : α → β) (a' : α) (b : β) (a : α) :
    update f a' b a = if a = a' then b else f a :=
by have h2 : (h : a = a') → Eq.rec (motive := λ _ _ => β) b h.symm = b :=
     by intro h; cases h; simp
   have h3 : (λ h : a = a' => Eq.rec (motive := λ _ _ => β) b h.symm) =
             (λ _ : a = a' =>  b) := funext h2
   let f := λ x => dite (a = a') x (λ (_: ¬ a = a') => (f a))
   exact congrArg f h3

@[simp]
theorem update_same (a : α) (v : β a) (f : ∀ a, β a) : update f a v a = v :=
  dif_pos rfl

@[simp]
theorem update_noteq {a a' : α} (h : a ≠ a') (v : β a') (f : ∀ a, β a) : update f a' v a = f a :=
  dif_neg h

theorem forall_update_iff (f : ∀a, β a) {a : α} {b : β a} (p : ∀a, β a → Prop) :
  (∀ x, p x (update f a b x)) ↔ p a b ∧ ∀ x, x ≠ a → p x (f x) := by
  rw [← Decidable.and_forall_ne a, update_same]
  simp (config := { contextual := true })

theorem exists_update_iff (f : ∀ a, β a) {a : α} {b : β a} (p : ∀ a, β a → Prop) [∀ a b, Decidable (p a b)] :
    (∃ x, p x (update f a b x)) ↔ p a b ∨ ∃ (x : _) (_ : x ≠ a), p x (f x) := by
  if h : p a b then
    simp [h]; refine ⟨a,?_⟩; simp [h]
  else
    simp [h]
    apply exists_congr
    intro a'
    if h' : a' = a then
      cases h'; simp [h]
    else
      simp [h']

theorem update_eq_iff {a : α} {b : β a} {f g : ∀ a, β a} :
    update f a b = g ↔ b = g a ∧ ∀ (x) (_ : x ≠ a), f x = g x :=
  funext_iff.trans <| forall_update_iff _ fun x y ↦ y = g x

theorem eq_update_iff {a : α} {b : β a} {f g : ∀ a, β a} :
    g = update f a b ↔ g a = b ∧ ∀ (x) (_ : x ≠ a), g x = f x :=
  funext_iff.trans <| forall_update_iff _ fun x y ↦ g x = y

@[simp] theorem update_eq_self_iff : update f a b = f ↔ b = f a := by simp [update_eq_iff]

@[simp] theorem eq_update_self_iff : f = update f a b ↔ f a = b := by simp [eq_update_iff]

theorem ne_update_self_iff : f ≠ update f a b ↔ f a ≠ b := by unfold Ne; rw [eq_update_self_iff]

theorem update_ne_self_iff : update f a b ≠ f ↔ b ≠ f a := by unfold Ne; rw [update_eq_self_iff]

@[simp]
theorem update_eq_self (a : α) (f : ∀ a, β a) : update f a (f a) = f :=
  update_eq_iff.2 ⟨rfl, fun _ _ ↦ rfl⟩

theorem update_comp_eq_of_forall_ne' {α'} (g : ∀ a, β a) {f : α' → α} {i : α} (a : β i)
    (h : ∀ x, f x ≠ i) : (fun j ↦ (update g i a) (f j)) = fun j ↦ g (f j) :=
  funext fun _ ↦ update_noteq (h _) _ _

/-- Non-dependent version of `Function.update_comp_eq_of_forall_ne'` -/
theorem update_comp_eq_of_forall_ne {α β : Sort _} (g : α' → β) {f : α → α'} {i : α'} (a : β)
    (h : ∀ x, f x ≠ i) : update g i a ∘ f = g ∘ f :=
  update_comp_eq_of_forall_ne' g a h

theorem apply_update {ι : Sort _} [DecidableEq ι] {α β : ι → Sort _} (f : ∀ i, α i → β i)
    (g : ∀ i, α i) (i : ι) (v : α i) (j : ι) :
    f j (update g i v j) = update (fun k ↦ f k (g k)) i (f i v) j := by
  by_cases h:j = i
  · subst j
    simp
  · simp [h]

theorem apply_update₂ {ι : Sort _} [DecidableEq ι] {α β γ : ι → Sort _} (f : ∀ i, α i → β i → γ i)
    (g : ∀ i, α i) (h : ∀ i, β i) (i : ι) (v : α i) (w : β i) (j : ι) :
    f j (update g i v j) (update h i w j) = update (fun k ↦ f k (g k) (h k)) i (f i v w) j := by
  by_cases h:j = i
  · subst j
    simp
  · simp [h]

theorem comp_update {α' : Sort _} {β : Sort _} (f : α' → β) (g : α → α') (i : α) (v : α') :
    f ∘ update g i v = update (f ∘ g) i (f v) :=
  funext <| apply_update _ _ _ _

theorem update_comm {α} [DecidableEq α] {β : α → Sort _} {a b : α} (h : a ≠ b) (v : β a) (w : β b)
    (f : ∀ a, β a) : update (update f a v) b w = update (update f b w) a v := by
  funext c
  simp only [update]
  by_cases h₁ : c = b <;> by_cases h₂ : c = a
  · rw [dif_pos h₁, dif_pos h₂]
    cases h (h₂.symm.trans h₁)
  · rw [dif_pos h₁, dif_pos h₁, dif_neg h₂]
  · rw [dif_neg h₁, dif_neg h₁, dif_pos h₂]
  · rw [dif_neg h₁, dif_neg h₁, dif_neg h₂]

@[simp]
theorem update_idem {α} [DecidableEq α] {β : α → Sort _} {a : α} (v w : β a) (f : ∀ a, β a) :
    update (update f a v) a w = update f a w := by
  funext b
  by_cases h : b = a <;> simp [update, h]

end Update

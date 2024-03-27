/-
Copyright (c) 2023 Wojciech Nawrocki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Nawrocki
-/

import Std.Data.List.Basic
import Std.Data.List.Pairwise
import Std.Data.List.Perm

/-- There is at most one element satisfying `p` in `l`. -/
def List.AtMostOne (p : α → Prop) (l : List α) : Prop :=
  l.Pairwise (p · → ¬p ·)

namespace List.AtMostOne

theorem of_cons {x : α} {l : List α} {p : α → Prop} :
    (x :: l).AtMostOne p → p x → ∀ y ∈ l, ¬p y :=
  fun h hP _ hY => rel_of_pairwise_cons h hY hP

theorem sublist {l₁ l₂ : List α} {p : α → Prop} :
    l₁ <+ l₂ → l₂.AtMostOne p → l₁.AtMostOne p :=
  Pairwise.sublist

theorem perm {l₁ l₂ : List α} {p : α → Prop} : l₁ ~ l₂ →
    l₁.AtMostOne p → l₂.AtMostOne p :=
  fun h h₁ => h.pairwise h₁ fun H hB hA => H hA hB

theorem imp {l : List α} {p q : α → Prop} (H : ∀ a, p a → q a) :
    l.AtMostOne q → l.AtMostOne p :=
  Pairwise.imp fun h hpa hpb => h (H _ hpa) (H _ hpb)

theorem find?_eq_of_perm {l₁ l₂ : List α} {p : α → Bool} :
    l₁.AtMostOne (p ·) → l₁ ~ l₂ → l₁.find? p = l₂.find? p := by
  intro hUniq h
  induction h using Perm.recOnSwap' with
  | nil => rfl
  | @cons x l₁ _ _ ih =>
    have := ih (hUniq.sublist (sublist_cons x l₁))
    simp [find?, this]
  | @swap' x y l₁ l₂ _ ih =>
    dsimp [find?]
    split <;> split <;> try rfl
    next hY _ hX =>
      have : ¬p x := hUniq.of_cons hY x (mem_cons_self _ _)
      contradiction
    next => exact ih <| hUniq.sublist <| sublist_of_cons_sublist <| sublist_cons y (x :: l₁)
  | trans h₁₂ _ h₁ h₂ =>
    simp [h₁ hUniq, h₂ (hUniq.perm h₁₂)]

/-- If there is at most one element with the property `p`,
finding that one element is the same as finding any. -/
theorem find?_eq_some_iff {l : List α} {a : α} {p : α → Bool} :
    l.AtMostOne (p ·)  → (l.find? p = some a ↔ (a ∈ l ∧ p a)) := by
  refine fun h => ⟨fun h' => ⟨mem_of_find?_eq_some h', find?_some h'⟩, ?_⟩
  induction l with
  | nil => simp
  | cons x xs ih =>
    intro ⟨hMem, hP⟩
    cases mem_cons.mp hMem with
    | inl hX => simp [find?, ← hX, hP]
    | inr hXs =>
      unfold find?
      cases hPX : (p x) with
      | false =>
        apply ih (Pairwise.sublist (sublist_cons x xs) h) ⟨hXs, hP⟩
      | true =>
        have := pairwise_cons.mp h |>.left a hXs hPX
        contradiction

/-- If there is at most one element with the property `p`,
erasing one such element is the same as filtering out all of them. -/
theorem eraseP_eq_filter (l : List α) (p : α → Bool) :
    l.AtMostOne (p ·) → l.eraseP p = l.filter (!p ·) := by
  intro h
  induction l with
  | nil => rfl
  | cons x xs ih =>
    specialize ih (Pairwise.sublist (sublist_cons x xs) h)
    cases hP : p x with
    | true =>
      rw [AtMostOne, pairwise_cons] at h
      have : ∀ a ∈ xs, !p a := fun a hA => by
        have := h.left a hA hP
        simp only [Bool.not_eq_true, Bool.not_eq_true'] at this ⊢
        exact this
      simp [eraseP, filter, hP, filter_eq_self.mpr this]
    | false => simp [eraseP_cons, filter, hP, ih]

theorem replaceF_perm {a b : α} {l : List α} (f : α → Option α) :
    l.AtMostOne (fun a => (f a).isSome) →
    a ∈ l → f a = some b →
    l.replaceF f ~ b :: l.eraseP (f · |>.isSome) := by
  intro hAmo hMem hF
  induction l with
  | nil => cases hMem
  | cons x xs ih =>
    unfold replaceF eraseP
    cases mem_cons.mp hMem with
    | inl hMem => simp [← hMem, hF, Perm.refl]
    | inr hMem =>
      have : f x = none := by
        have .cons hAmo _ := hAmo
        exact Option.eq_none_iff_forall_not_mem.mpr fun b hB' =>
          have h₁ : (f x).isSome := hB' ▸rfl
          have h₂ : (f a).isSome := hF ▸ Option.isSome_some
          hAmo a hMem h₁ h₂
      simp only [this, Option.isSome_none, cond_false]
      have := ih (hAmo.sublist <| sublist_cons _ _) hMem
      exact .trans (.cons x this) (.swap b x _)

end List.AtMostOne

/-
Copyright (c) 2014 Parikshit Khanna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Parikshit Khanna, Jeremy Avigad, Leonardo de Moura, Floris van Doorn, Mario Carneiro
-/

/-! # Bootstrapping properties of Lists -/

namespace List

@[ext] theorem ext : ∀ {l₁ l₂ : List α}, (∀ n, l₁.get? n = l₂.get? n) → l₁ = l₂
  | [], [], _ => rfl
  | a :: l₁, [], h => nomatch h 0
  | [], a' :: l₂, h => nomatch h 0
  | a :: l₁, a' :: l₂, h => by
    have h0 : some a = some a' := h 0
    injection h0 with aa; simp only [aa, ext fun n => h (n+1)]

theorem ext_get {l₁ l₂ : List α} (hl : length l₁ = length l₂)
    (h : ∀ n h₁ h₂, get l₁ ⟨n, h₁⟩ = get l₂ ⟨n, h₂⟩) : l₁ = l₂ :=
  ext fun n =>
    if h₁ : n < length l₁ then by
      rw [get?_eq_get, get?_eq_get, h n h₁ (by rwa [← hl])]
    else by
      have h₁ := Nat.le_of_not_lt h₁
      rw [get?_len_le h₁, get?_len_le]; rwa [← hl]

@[simp] theorem get_map (f : α → β) {l n} : get (map f l) n = f (get l ⟨n, length_map l f ▸ n.2⟩) :=
  Option.some.inj <| by rw [← get?_eq_get, get?_map, get?_eq_get]; rfl

/-! ### foldl / foldr -/

theorem foldl_map (f : β₁ → β₂) (g : α → β₂ → α) (l : List β₁) (init : α) :
    (l.map f).foldl g init = l.foldl (fun x y => g x (f y)) init := by
  induction l generalizing init <;> simp [*]

theorem foldr_map (f : α₁ → α₂) (g : α₂ → β → β) (l : List α₁) (init : β) :
    (l.map f).foldr g init = l.foldr (fun x y => g (f x) y) init := by
  induction l generalizing init <;> simp [*]

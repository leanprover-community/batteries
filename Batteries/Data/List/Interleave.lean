/-
Copyright (c) 2026 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Batteries.Data.List.Lemmas

/-!
# Interleaving lists

This file defines interleaving of lists, both as an operation and as a relation.
-/

public section

namespace List
variable {α : Type u} {r s : α → α → Prop} {l l₁ l₂ : List α} {a b c : α}

/-- Interleaves two lists `l₁` and `l₂`, starting with an element of `l₂`.
This operation is well-behaved only when the length of `l₂` is either the length of `l₁`
or one more.
```
#eval interleave [1, 3] [0, 2, 4] -- [0, 1, 2, 3, 4]
#eval interleave [0, 1, 2] [3, 4]
```
-/
@[expose]
def interleave : List α → List α → List α
  | _, [] => []
  | l₁, a :: l₂ => a :: interleave l₂ l₁
termination_by l₁ l₂ => l₁.length + l₂.length

@[simp] theorem interleave_nil (l₁ : List α) : l₁.interleave [] = [] := by rw [interleave]

@[simp]
theorem interleave_cons (l₁ : List α) (a : α) (l₂ : List α) :
    l₁.interleave (a :: l₂) = a :: interleave l₂ l₁ := by rw [interleave]

@[simp]
theorem interleave_append_append_of_length_eq_length :
    ∀ {l₁ l₂ : List α} (_h₁₂ : l₁.length = l₂.length) (l₃ l₄ : List α),
      (l₁ ++ l₃).interleave (l₂ ++ l₄) = l₁.interleave l₂ ++ l₃.interleave l₄
  | [], [], _, l₃, l₄ => by simp
  | a :: l₁, b :: l₂, _, l₃, l₄ => by simp_all [interleave_append_append_of_length_eq_length]

@[simp]
theorem interleave_append_append_of_length_add_one_eq_length :
    ∀ {l₁ l₂ : List α} (_h₁₂ : l₁.length + 1 = l₂.length) (l₃ l₄ : List α),
      (l₁ ++ l₃).interleave (l₂ ++ l₄) = l₁.interleave l₂ ++ l₄.interleave l₃
  | [], b :: l₂, _, l₃, l₄ => by simp_all
  | a :: l₁, b :: c :: l₂, _, l₃, l₄ => by simp_all [interleave_append_append_of_length_eq_length]

@[simp]
theorem left_sublist_interleave : ∀ {l₁ l₂ : List α}, l₁.length ≤ l₂.length → l₁ <+ l₁.interleave l₂
  | [], _, _ => by simp
  | a :: l₁, b :: l₂, h => by
    simp only [interleave_cons]
    exact .cons _ <| .cons_cons _ <| left_sublist_interleave <| by simpa using h

@[simp]
theorem right_sublist_interleave {l₁ l₂ : List α} (hl : l₂.length ≤ l₁.length + 1) :
    l₂ <+ l₁.interleave l₂ := by cases l₂ <;> simp_all

variable (r) in
/-- Relation for interleaving lists. `l₁` `r`-interleaves `l₂` if the length of `l₂` is either the
length of `l₁` or one more and if the `i`-th rightmost element of `l₁` is `r`-related to both the
`i`-th and `i + 1`-st rightmost elements of `l₂`, except possibly when `i = l₁.length`.

For example, `[1, 3]` `(· ≥ ·)`-interleaves `[0, 2, 4]`.

See `interleaves_iff_length_isChain_interleave` for the connection with `List.interleave`. -/
inductive Interleaves : List α → List α → Prop
  /-- The empty list interleaves itself. -/
  | nil_nil : Interleaves [] []
  /-- The empty list interleaves any singleton list. -/
  | nil_singleton (a : α) : Interleaves [] [a]
  /-- If `l₁` interleaves `b :: l₂` and `a` is related to `b`, then `b :: l₂` interleaves
  `a :: l₁`. -/
  | cons_symm ⦃l₁ l₂ : List α⦄ ⦃b : α⦄ (hl : Interleaves l₁ (b :: l₂)) ⦃a : α⦄ (hab : r a b) :
      Interleaves (b :: l₂) (a :: l₁)

attribute [simp] Interleaves.nil_nil
attribute [simp high] Interleaves.nil_singleton

theorem interleaves_iff :
  Interleaves r l₁ l₂ ↔
    l₁ = [] ∧ l₂ = [] ∨
      (∃ a, l₁ = [] ∧ l₂ = [a]) ∨ ∃ l₁' l₂' b, Interleaves r l₁' (b :: l₂') ∧ ∃ a, r a b ∧ l₁ = b :: l₂' ∧ l₂ = a :: l₁' where
  mp
  | .nil_nil => by simp
  | .nil_singleton a => by simp
  | .cons_symm hl hab => .inr <| .inr <| ⟨_, _, _, hl, _, hab, rfl, rfl⟩
  mpr := by simp +contextual [or_imp, Interleaves.cons_symm]

@[simp]
theorem interleaves_nil_cons : Interleaves r [] (a :: l) ↔ l = [] := by grind [interleaves_iff]

@[simp]
theorem not_interleaves_cons_nil : ¬ Interleaves r (a :: l) [] := by grind [interleaves_iff]

@[simp]
theorem interleaves_singleton_singleton : Interleaves r [a] [b] ↔ r b a := by grind [interleaves_iff]

theorem Interleaves.mono (hrs : ∀ ⦃a b⦄, r a b → s a b) :
    ∀ l₁ l₂ : List α, Interleaves r l₁ l₂ → Interleaves s l₁ l₂
  | _, _, .nil_nil => .nil_nil
  | _, _, .nil_singleton a => .nil_singleton _
  | _, _, .cons_symm hl hab => .cons_symm (hl.mono hrs) <| hrs hab

theorem interleaves_iff_length_isChain_interleave :
    ∀ {l₁ l₂ : List α},
    Interleaves r l₁ l₂ ↔
      (l₁.length = l₂.length ∨ l₁.length + 1 = l₂.length) ∧ (l₁.interleave l₂).IsChain r
  | [], [] => by simp
  | [], b :: l₂ => by simp
  | a :: l₁, [] => by simp
  | a :: l₁, [b] => by
    rw [interleaves_iff]
    simp
    constructor
    · rintro ⟨_, _, _, hl, _, hba, ⟨rfl, rfl⟩, rfl, rfl⟩
      simp_all
    · rintro ⟨rfl, hba⟩
      exact ⟨_, _, _, by simp, _, hba, ⟨rfl, rfl⟩, rfl, rfl⟩
  | a :: l₁, b :: l₂ => by
    rw [interleaves_iff]
    simp only [reduceCtorEq, and_self, cons.injEq, false_and, exists_false, false_or, length_cons,
      Nat.add_right_cancel_iff, interleave_cons, isChain_cons_cons]
    constructor
    · rintro ⟨_, _, _, hl, _, hba, ⟨rfl, rfl⟩, rfl, rfl⟩
      rw [interleaves_iff_length_isChain_interleave] at hl
      simp_all [or_comm, eq_comm]
    · rintro ⟨h | h, hba, hl⟩
      all_goals
        refine ⟨_, _, _, ?_, _, hba, ⟨rfl, rfl⟩, rfl, rfl⟩
        rw [interleaves_iff_length_isChain_interleave]
        simp_all
termination_by l₁ l₂ => l₁.length + l₂.length

variable [Trans r r r]

theorem Interleaves.pairwise_left (hl : Interleaves r l₁ l₂) : l₁.Pairwise r := by
  rw [interleaves_iff_length_isChain_interleave] at hl
  exact hl.2.pairwise.sublist <| left_sublist_interleave <| by lia

theorem Interleaves.pairwise_right (hl : Interleaves r l₁ l₂) : l₂.Pairwise r := by
  rw [interleaves_iff_length_isChain_interleave] at hl
  exact hl.2.pairwise.sublist <| right_sublist_interleave <| by lia

end List

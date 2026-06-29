/-
Copyright (c) 2026 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

/-!
# Interleaving lists

This file defines interleaving of lists as an operation.
-/

public section

namespace List
variable {α : Type u} {r s : α → α → Prop} {l l₁ l₂ l₃ l₄ : List α} {a b c : α}

/-- Interleave two lists `l₁` and `l₂`, starting with an element of `l₁`.

This operation fully interleave the two lists when the length of `l₁` is either the length of `l₂`
or one more. If one of the lists runs out early, the remainder of the other list is kept without
further interleaving, so that `l₁.interleave l₂` is always a permutation of `l₁ ++ l₂`.
See `interleave_perm_append`.

```
#eval interleave [0, 2, 4] [1] -- [0, 1, 2, 4] -- The second list is too short
#eval interleave [0, 2, 4] [1, 3] -- [0, 1, 2, 3, 4]
#eval interleave [0, 2] [1, 3] -- [0, 1, 2, 3]
#eval interleave [0] [1, 3] -- [0, 1, 3] -- The first list is too short
```
-/
@[expose]
def interleave : List α → List α → List α
  | [], l₂ => l₂
  | a :: l₁, l₂ => a :: interleave l₂ l₁
termination_by l₁ l₂ => l₁.length + l₂.length

@[simp] theorem nil_interleave (l₂ : List α) : [].interleave l₂ = l₂ := by rw [interleave]
@[simp] theorem interleave_nil (l₁ : List α) : l₁.interleave [] = l₁ := by
  cases l₁ <;> simp [interleave]

@[simp]
theorem cons_interleave (a : α) (l₁ : List α) (l₂ : List α) :
    (a :: l₁).interleave l₂ = a :: interleave l₂ l₁ := by rw [interleave]

@[simp] theorem interleave_perm_append : ∀ {l₁ l₂ : List α}, l₁.interleave l₂ ~ l₁ ++ l₂
  | [], l₂ => by simp
  | a :: l₁, l₂ => by
    rw [cons_interleave]
    exact ((interleave_perm_append ..).trans perm_append_comm).cons _
termination_by l₁ l₂ => l₁.length + l₂.length

protected theorem Perm.interleave (h₁₃ : l₁ ~ l₃) (h₂₄ : l₂ ~ l₄) :
    l₁.interleave l₂ ~ l₃.interleave l₄ :=
  interleave_perm_append.trans <| (h₁₃.append h₂₄).trans interleave_perm_append.symm

@[simp] theorem length_interleave (l₁ l₂ : List α) :
    (l₁.interleave l₂).length = l₁.length + l₂.length := by simp [interleave_perm_append.length_eq]

@[simp] theorem countP_interleave (l₁ l₂ : List α) (p : α → Bool) :
    (l₁.interleave l₂).countP p = l₁.countP p + l₂.countP p := by
  simp [interleave_perm_append.countP_eq]

@[simp] theorem count_interleave [BEq α] (l₁ l₂ : List α) (a : α) :
    (l₁.interleave l₂).count a = l₁.count a + l₂.count a := by
  simp [interleave_perm_append.count_eq]

@[simp]
theorem interleave_append_append_of_length_eq_length :
    ∀ {l₁ l₂ : List α} (_h₁₂ : l₁.length = l₂.length) (l₃ l₄ : List α),
      (l₁ ++ l₃).interleave (l₂ ++ l₄) = l₁.interleave l₂ ++ l₃.interleave l₄
  | [], [], _, l₃, l₄ => by simp
  | a :: l₁, b :: l₂, _, l₃, l₄ => by simp_all [interleave_append_append_of_length_eq_length]

@[simp]
theorem interleave_append_append_of_length_eq_length_add_one :
    ∀ {l₁ l₂ : List α} (_h₁₂ : l₁.length = l₂.length + 1) (l₃ l₄ : List α),
      (l₁ ++ l₃).interleave (l₂ ++ l₄) = l₁.interleave l₂ ++ l₄.interleave l₃
  | a :: l₁, l₂, _, l₃, l₄ => by simp_all

@[simp]
theorem interleave_append_left :
    ∀ {l₁ l₂ : List α} (_h₂₁ : l₂.length ≤ l₁.length) (l₃ : List α),
      (l₁ ++ l₃).interleave l₂ = l₁.interleave l₂ ++ l₃
  | _, [], _, l₃ => by simp
  | a :: l₁, b :: l₂, _, l₃ => by simp_all [interleave_append_left]

@[simp]
theorem interleave_append_right :
    ∀ {l₁ l₂ : List α} (_h₁₂ : l₁.length ≤ l₂.length + 1) (l₃ : List α),
    l₁.interleave (l₂ ++ l₃) = l₁.interleave l₂ ++ l₃
  | [], _, _, l₃ => by simp
  | [a], [], _, l₃ => by simp
  | a :: l₁, b :: l₂, _, l₃ => by simp_all [interleave_append_right]

@[simp]
theorem reverse_interleave_of_length_eq_length :
    ∀ {l₁ l₂ : List α}, l₁.length = l₂.length →
      (l₁.interleave l₂).reverse = l₂.reverse.interleave l₁.reverse
  | [], [], _ => by simp
  | a :: l₁, b :: l₂, _ => by simp_all [reverse_interleave_of_length_eq_length]

@[simp]
theorem reverse_interleave_of_length_eq_length_add_one :
    ∀ {l₁ l₂ : List α}, l₁.length = l₂.length + 1 →
      (l₁.interleave l₂).reverse = l₁.reverse.interleave l₂.reverse
  | a :: l₁, [], _ => by simp
  | a :: l₁, b :: l₂, _ => by simp_all [reverse_interleave_of_length_eq_length_add_one]

@[simp]
theorem interleave_ofFn_ofFn_even :
    ∀ {n : Nat} {f g : Fin n → α},
      interleave (ofFn f) (ofFn g) =
        ofFn (n := 2 * n) (fun i => if i.val % 2 = 0 then f ⟨i / 2, by lia⟩ else g ⟨i / 2, by lia⟩)
  | 0, f, g  => by simp
  | n + 1, f, g => by simp_all [interleave_ofFn_ofFn_even]; grind

theorem interleave_ofFn_ofFn_odd :
    ∀ {n : Nat} {f : Fin (n + 1) → α} {g : Fin n → α},
      interleave (ofFn f) (ofFn g) =
        ofFn (n := 2 * n + 1)
          (fun i => if hi : i.val % 2 = 0 then f ⟨i / 2, by lia⟩ else g ⟨i / 2, by lia⟩)
  | 0, f, g  => by simp
  | n + 1, f, g => by simp_all [interleave_ofFn_ofFn_even]; grind

@[simp]
theorem right_sublist_interleave : ∀ {l₁ l₂ : List α}, l₂ <+ l₁.interleave l₂
  | _, [] => by simp
  | [], _ => by simp
  | a :: l₁, b :: l₂ => by
    simp only [cons_interleave]
    exact .cons _ <| right_sublist_interleave.cons_cons _

@[simp]
theorem left_sublist_interleave : l₁ <+ l₁.interleave l₂ := by cases l₁ <;> simp_all

@[simp]
protected theorem IsPrefix.interleave {l₁ l₂ l₃ l₄ : List α} :
    l₁.length = l₂.length ∨ l₁.length = l₂.length + 1 →
    l₁ <+: l₃ → l₂ <+: l₄ → l₁.interleave l₂ <+: l₃.interleave l₄ := by
  rintro (hl | hl) ⟨l₅, rfl⟩ ⟨l₆, rfl⟩ <;>
    simp [interleave_append_append_of_length_eq_length,
      interleave_append_append_of_length_eq_length_add_one, hl]

end List

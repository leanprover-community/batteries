/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg, François G. Dorais
-/
import Batteries.Classes.Order

-- Forward port of lean4#9515
@[grind ←]
theorem List.mem_finRange (x : Fin n) : x ∈ finRange n := by
  simp [finRange]

namespace Char

theorem le_antisymm_iff {x y : Char} : x = y ↔ x ≤ y ∧ y ≤ x :=
  Char.ext_iff.trans UInt32.le_antisymm_iff

instance : Std.LawfulOrd Char :=
  .compareOfLessAndEq_of_irrefl_of_trans_of_not_lt_of_antisymm
    (fun _ => Nat.lt_irrefl _) Nat.lt_trans Nat.not_lt Char.le_antisymm

@[simp] theorem toNat_val (c : Char) : c.val.toNat = c.toNat := rfl

@[simp] theorem toNat_ofNatAux {n : Nat} (h : n.isValidChar) : toNat (ofNatAux n h) = n := by
  simp [ofNatAux, toNat]

theorem toNat_ofNat (n : Nat) : toNat (ofNat n) = if n.isValidChar then n else 0 := by
  split
  · simp [ofNat, *]
  · simp [ofNat, toNat, *]

/-- Returns `true` if `p` returns true for every `Char`. -/
protected def all (p : Char → Bool) : Bool :=
  -- Recall that character code points range from 0 to 0x10FFFF, excluding the surrogate range from
  -- 0xD800 to 0xDFFF.
  -- (See [Unicode scalar value](https://www.unicode.org/glossary/#unicode_scalar_value).)
  Nat.all 0xD800 (fun c h₁ => p <| Char.ofNatAux c <| .inl h₁) &&
  Nat.all (0x110000 - 0xE000) fun c h₂ => p <| Char.ofNatAux (c + 0xE000) <| .inr (by grind)

private theorem of_all_eq_true_aux (h : Char.all p) (n : Nat) (hn : n.isValidChar) :
    p (.ofNatAux n hn) := by
  simp only [Char.all, Nat.all_eq_finRange_all, List.all_eq_true, Bool.and_eq_true] at h
  simp only [Nat.isValidChar] at hn
  match hn with
  | .inl hn =>
    have h₁ := h.1 ⟨n, by grind⟩
    grind
  | .inr ⟨hn, hn'⟩ =>
    have h₂ := h.2 ⟨n - 0xE000, by omega⟩
    simp only [Nat.reduceSub, List.mem_finRange, Nat.sub_add_cancel hn, forall_const] at h₂
    exact h₂

theorem eq_true_of_all_eq_true (h : Char.all p) (c : Char) : p c := by
  have : c.toNat.isValidChar := c.valid
  rw [← c.ofNat_toNat, ofNat, dif_pos this]
  exact of_all_eq_true_aux h c.toNat this

theorem exists_eq_false_of_all_eq_false (h : Char.all p = false) :
    ∃ c, p c = false := by
  simp only [Char.all, Nat.all_eq_finRange_all, List.all_eq_false, Bool.and_eq_false_iff] at h
  simp only [Bool.eq_false_iff]
  match h with
  | .inl ⟨⟨n, hn⟩, _, h⟩ => exact ⟨Char.ofNatAux n (.inl hn), h⟩
  | .inr ⟨⟨n, _⟩, _, h⟩ => exact ⟨Char.ofNatAux (n + 0xE000) (.inr (by grind)), h⟩

theorem all_eq_true_iff_forall_eq_true : Char.all p = true ↔ ∀ c, p c = true := by
  constructor
  · exact eq_true_of_all_eq_true
  · intro h
    cases heq : Char.all p
    · obtain ⟨c, hc⟩ := exists_eq_false_of_all_eq_false heq
      simp [h c] at hc
    · trivial

/-- Returns `true` if `p` returns true for some `Char`. -/
protected def any (p : Char → Bool) : Bool :=
  -- Recall that character code points range from 0 to 0x10FFFF, excluding the surrogate range from
  -- 0xD800 to 0xDFFF.
  -- (See [Unicode scalar value](https://www.unicode.org/glossary/#unicode_scalar_value).)
  Nat.any 0xD800 (fun c h₁ => p <| Char.ofNatAux c <| .inl h₁) ||
  Nat.any (0x110000 - 0xE000) fun c h₂ => p <| Char.ofNatAux (c + 0xE000) <| .inr (by grind)

theorem exists_eq_true_of_any_eq_true (h : Char.any p = true) : ∃ c, p c = true := by
  simp only [Char.any, Nat.any_eq_finRange_any, List.any_eq_true, Bool.or_eq_true] at h
  match h with
  | .inl ⟨⟨n, hn⟩, _, h⟩ => exact ⟨Char.ofNatAux n (.inl hn), h⟩
  | .inr ⟨⟨n, _⟩, _, h⟩ => exact ⟨Char.ofNatAux (n + 0xE000) (.inr (by grind)), h⟩

private theorem of_any_eq_false_aux (h : Char.any p = false) (n : Nat) (hn : n.isValidChar) :
    p (.ofNatAux n hn) = false := by
  simp only [Char.any, Nat.any_eq_finRange_any, List.any_eq_false, Bool.or_eq_false_iff] at h
  simp only [Nat.isValidChar] at hn
  simp only [Bool.eq_false_iff]
  match hn with
  | .inl hn => exact h.1 ⟨n, hn⟩ (List.mem_finRange _)
  | .inr ⟨hn, hn'⟩ =>
    have h₂ := h.2 ⟨n - 0xE000, by omega⟩ (List.mem_finRange _)
    simp only [Nat.sub_add_cancel hn] at h₂
    exact h₂

theorem eq_false_of_any_eq_false (h : Char.any p = false) (c : Char) : p c = false := by
  have : c.toNat.isValidChar := c.valid
  rw [← c.ofNat_toNat, ofNat, dif_pos this]
  exact of_any_eq_false_aux h c.toNat this

theorem any_eq_true_iff_exists_eq_true : Char.any p = true ↔ ∃ c, p c = true := by
  constructor
  · exact exists_eq_true_of_any_eq_true
  · intro h
    cases heq : Char.any p
    · obtain ⟨c, hc⟩ := h
      simp [eq_false_of_any_eq_false heq] at hc
    · trivial

instance (P : Char → Prop) [DecidablePred P] : Decidable (∀ c, P c) :=
  match h : Char.all (P ·) with
  | true => isTrue <| fun c => of_decide_eq_true <| eq_true_of_all_eq_true h c
  | false => isFalse <| not_forall_of_exists_not <|
      match exists_eq_false_of_all_eq_false h with
      | ⟨c, hc⟩ => ⟨c, of_decide_eq_false hc⟩

instance (P : Char → Prop) [DecidablePred P] : Decidable (∃ c, P c) :=
  match h : Char.any (P ·) with
  | false => isFalse <| not_exists_of_forall_not <| fun c =>
      of_decide_eq_false <| eq_false_of_any_eq_false h c
  | true => isTrue <|
      match exists_eq_true_of_any_eq_true h with
      | ⟨c, hc⟩ => ⟨c, of_decide_eq_true hc⟩

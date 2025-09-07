/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg, François G. Dorais
-/
import Batteries.Classes.Order

-- Forward port of lean4#9515
theorem List.mem_finRange (x : Fin n) : x ∈ finRange n := by
  simp [finRange]

namespace Char

theorem le_antisymm_iff {x y : Char} : x = y ↔ x ≤ y ∧ y ≤ x :=
  Char.ext_iff.trans UInt32.le_antisymm_iff

instance : Batteries.LawfulOrd Char := .compareOfLessAndEq
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
  -- 0x10FFFF (1114111) is the maximal valid code point.
  Nat.all 0x110000 fun c h =>
    -- Surrogate code points are from 0xD800 (55296) to 0xDFFF (57343).
    if h₁ : c < 0xD800 then
      p <| Char.ofNatAux c <| .inl h₁
    else if h₂ : 0xDFFF < c then
      p <| Char.ofNatAux c <| .inr ⟨h₂, h⟩
    else
      true

private theorem of_all_eq_true_aux (h : Char.all p) (n : Nat) (hn : n.isValidChar) :
    p (.ofNatAux n hn) := by
  simp only [Char.all, Nat.all_eq_finRange_all, List.all_eq_true] at h
  simp only [Nat.isValidChar] at hn
  match hn with
  | .inl hn =>
    have hn' : n < 1114112 := by omega
    have := h ⟨n, hn'⟩ (List.mem_finRange _)
    rwa [dif_pos hn] at this
  | .inr ⟨hn, hn'⟩ =>
    have hn'' : ¬ n < 55296 := by omega
    have := h ⟨n, hn'⟩ (List.mem_finRange _)
    rwa [dif_neg hn'', dif_pos hn] at this

theorem eq_true_of_all_eq_true (h : Char.all p) (c : Char) : p c := by
  have : c.toNat.isValidChar := c.valid
  rw [← c.ofNat_toNat, ofNat, dif_pos this]
  exact of_all_eq_true_aux h c.toNat this

theorem exists_eq_false_of_all_eq_false (h : Char.all p = false) :
    ∃ c, p c = false := by
  simp only [Char.all, Nat.all_eq_finRange_all, List.all_eq_false] at h
  match h with
  | ⟨⟨n, hn⟩, ⟨_, h⟩⟩ =>
    simp only [Bool.eq_false_iff]
    split at h
    · refine ⟨ofNatAux n (.inl ?_), h⟩; assumption
    · split at h
      · refine ⟨ofNatAux n (.inr ⟨?_, hn⟩), h⟩; assumption
      · simp at h

/-- Returns `true` if `p` returns true for some `Char`. -/
protected def any (p : Char → Bool) : Bool :=
  -- 0x10FFFF (1114111) is the maximal valid code point.
  Nat.any 0x110000 fun c h =>
    -- Surrogate code points are from 0xD800 (55296) to 0xDFFF (57343).
    if h₁ : c < 0xD800 then
      p <| Char.ofNatAux c <| .inl h₁
    else if h₂ : 0xDFFF < c then
      p <| Char.ofNatAux c <| .inr ⟨h₂, h⟩
    else
      false

theorem exists_eq_true_of_any_eq_true (h : Char.any p = true) : ∃ c, p c = true := by
  simp only [Char.any, Nat.any_eq_finRange_any, List.any_eq_true] at h
  match h with
  | ⟨⟨n, hn⟩, ⟨_, h⟩⟩ =>
    split at h
    · refine ⟨ofNatAux n (.inl ?_), h⟩; assumption
    · split at h
      · refine ⟨ofNatAux n (.inr ⟨?_, hn⟩), h⟩; assumption
      · simp at h

private theorem of_any_eq_false_aux (h : Char.any p = false) (n : Nat) (hn : n.isValidChar) :
    p (.ofNatAux n hn) = false := by
  simp only [Char.any, Nat.any_eq_finRange_any, List.any_eq_false] at h
  simp only [Nat.isValidChar] at hn
  match hn with
  | .inl hn =>
    have hn' : n < 1114112 := by omega
    have := h ⟨n, hn'⟩ (List.mem_finRange _)
    rwa [← ne_eq, ← Bool.eq_false_iff, dif_pos hn] at this
  | .inr ⟨hn, hn'⟩ =>
    have hn'' : ¬ n < 55296 := by omega
    have := h ⟨n, hn'⟩ (List.mem_finRange _)
    rwa [← ne_eq, ← Bool.eq_false_iff, dif_neg hn'', dif_pos hn] at this

theorem eq_false_of_any_eq_false (h : Char.any p = false) (c : Char) : p c = false := by
  have : c.toNat.isValidChar := c.valid
  rw [← c.ofNat_toNat, ofNat, dif_pos this]
  exact of_any_eq_false_aux h c.toNat this

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

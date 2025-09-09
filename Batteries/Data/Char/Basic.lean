/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/
import Batteries.Classes.Order

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

/--
Maximum character code point.
(See [unicode scalar value](https://www.unicode.org/glossary/#unicode_scalar_value).)
-/
protected abbrev max := 0x10FFFF

/--
Maximum surrogate code point.
(See [unicode scalar value](https://www.unicode.org/glossary/#unicode_scalar_value).)
-/
protected abbrev maxSurrogate := 0xDFFF

/--
Minimum surrogate code point.
(See [unicode scalar value](https://www.unicode.org/glossary/#unicode_scalar_value).)
-/
protected abbrev minSurrogate := 0xD800

/--
Number of valid character code points.
(See [unicode scalar value](https://www.unicode.org/glossary/#unicode_scalar_value).)
-/
protected abbrev count := Char.max - Char.maxSurrogate + Char.minSurrogate

@[grind] theorem toNat_le_max (c : Char) : c.toNat ≤ Char.max := by
  match c.valid with
  | .inl h => simp only [toNat_val] at h; grind
  | .inr ⟨_, h⟩ => simp only [toNat_val] at h; grind

@[grind] theorem toNat_not_surrogate (c : Char) :
    ¬(Char.minSurrogate ≤ c.toNat ∧ c.toNat ≤ Char.maxSurrogate) := by
  match c.valid with
  | .inl h => simp only [toNat_val] at h; grind
  | .inr ⟨h, _⟩ => simp only [toNat_val] at h; grind

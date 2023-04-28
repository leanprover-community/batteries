/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Std.Data.Char
import Std.Data.Nat.Lemmas

namespace Substring

/--
If `pre` is a prefix of `s`, i.e. `s = pre ++ t`, return the remainder `t`.
-/
def dropPrefix? (s : Substring) (pre : Substring) : Option Substring :=
  go 0 (pre.stopPos - pre.startPos)
where
  /-- Auxiliary definition for `dropPrefix?`. -/
  go (start : String.Pos) (stop : String.Pos) : Option Substring :=
    if h : start ≥ stop then
      some { s with startPos := s.startPos + start }
    else
      let cs := s.get start
      let cp := pre.get start
      if cs == cp then
        have : start.byteIdx + String.csize cs ≤ stop.byteIdx + 4 :=
          Nat.add_le_add (Nat.le_of_lt $ Nat.not_le.mp h) (Char.csize_le_4 _)
        have : stop.byteIdx + 4 - (start.byteIdx + String.csize cs) <
                stop.byteIdx + 4 - start.byteIdx :=
          Nat.sub_add_lt_sub this (Char.csize_pos _)
        go (start + cs) stop
      else
        none
termination_by go start stop => stop.byteIdx + 4 - start.byteIdx

end Substring

namespace String

@[simp]
theorem Pos.byteIdx_zero : (0 : Pos).byteIdx = 0 :=
  rfl

@[simp]
theorem Pos.mk_zero : ⟨0⟩ = (0 : Pos) :=
  rfl

@[simp]
theorem Pos.eq_iff {i₁ i₂ : Pos} : i₁ = i₂ ↔ i₁.byteIdx = i₂.byteIdx :=
  ⟨fun h ↦ h ▸ rfl, fun h ↦ show ⟨i₁.byteIdx⟩ = (⟨i₂.byteIdx⟩ : Pos) from h ▸ rfl⟩

@[simp]
theorem Pos.add_eq (p₁ p₂ : Pos) : p₁ + p₂ = ⟨p₁.byteIdx + p₂.byteIdx⟩ :=
  rfl

@[simp]
theorem Pos.sub_eq (p₁ p₂ : Pos) : p₁ - p₂ = ⟨p₁.byteIdx - p₂.byteIdx⟩ :=
  rfl

@[simp]
theorem Pos.add_char (p : Pos) (c : Char) : p + c = ⟨p.byteIdx + csize c⟩ :=
  rfl

@[simp]
theorem Pos.zero_add_char (c : Char) : (0 : Pos) + c = ⟨csize c⟩ := by
  simp

@[simp]
theorem Pos.add_string (p : Pos) (s : String) : p + s = ⟨p.byteIdx + s.utf8ByteSize⟩ :=
  rfl

@[simp]
theorem Pos.zero_add_string (s : String) : (0 : Pos) + s = ⟨s.utf8ByteSize⟩ := by
  simp

@[simp]
theorem Pos.le_iff {i₁ i₂ : Pos} : i₁ ≤ i₂ ↔ i₁.byteIdx ≤ i₂.byteIdx :=
  ⟨id, id⟩

@[simp]
theorem Pos.lt_iff {i₁ i₂ : Pos} : i₁ < i₂ ↔ i₁.byteIdx < i₂.byteIdx :=
  ⟨id, id⟩

/-- Induction on `String.utf8GetAux`. -/
def utf8GetAux.inductionOn.{u} {motive : List Char → Pos → Pos → Sort u}
    (s : List Char) (i p : Pos)
    (nil : ∀ i p, motive [] i p)
    (eq  : ∀ c cs i p, i = p → motive (c :: cs) i p)
    (ind : ∀ c cs i p, i ≠ p → motive cs ⟨i.byteIdx + csize c⟩ p → motive (c :: cs) i p) :
    motive s i p :=
  match s with
  | [] => nil i p
  | c::cs =>
    if h : i = p then
      eq c cs i p h
    else ind c cs i p h (inductionOn cs ⟨i.byteIdx + csize c⟩ p nil eq ind)

/--
If `pre` is a prefix of `s`, i.e. `s = pre ++ t`, return the remainder `t`.
-/
def dropPrefix? (s : String) (pre : String) : Option Substring :=
  s.toSubstring.dropPrefix? pre.toSubstring

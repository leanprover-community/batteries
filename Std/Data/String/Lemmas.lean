/-
Copyright (c) 2023 Bulhwi Cha. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bulhwi Cha
-/

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
  simp only [String.Pos.add_char, String.Pos.byteIdx_zero, Nat.zero_add]

@[simp]
theorem Pos.add_string (p : Pos) (s : String) : p + s = ⟨p.byteIdx + s.utf8ByteSize⟩ :=
  rfl

@[simp]
theorem Pos.zero_add_string (s : String) : (0 : Pos) + s = ⟨s.utf8ByteSize⟩ := by
  simp only [String.Pos.add_string, String.Pos.byteIdx_zero, Nat.zero_add]

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

end String

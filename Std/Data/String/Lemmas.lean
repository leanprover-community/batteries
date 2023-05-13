/-
Copyright (c) 2023 Bulhwi Cha. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bulhwi Cha
-/
import Std.Data.Char
import Std.Data.Nat.Lemmas
import Std.Tactic.Ext.Attr
import Std.Tactic.Simpa

namespace String

@[ext] theorem ext {s₁ s₂ : String} (h : s₁.data = s₂.data) : s₁ = s₂ :=
  show ⟨s₁.data⟩ = (⟨s₂.data⟩ : String) from h ▸ rfl

theorem ext_iff {s₁ s₂ : String} : s₁ = s₂ ↔ s₁.data = s₂.data := ⟨fun h => h ▸ rfl, ext⟩

namespace Pos

@[simp] theorem byteIdx_zero : (0 : Pos).byteIdx = 0 := rfl

theorem byteIdx_mk (n : Nat) : byteIdx ⟨n⟩ = n := rfl

@[simp] theorem mk_zero : ⟨0⟩ = (0 : Pos) := rfl

@[simp] theorem mk_byteIdx (p : Pos) : ⟨p.byteIdx⟩ = p := rfl

@[ext] theorem ext {i₁ i₂ : Pos} (h : i₁.byteIdx = i₂.byteIdx) : i₁ = i₂ :=
  show ⟨i₁.byteIdx⟩ = (⟨i₂.byteIdx⟩ : Pos) from h ▸ rfl

theorem ext_iff {i₁ i₂ : Pos} : i₁ = i₂ ↔ i₁.byteIdx = i₂.byteIdx := ⟨fun h => h ▸ rfl, ext⟩

@[simp] theorem add_byteIdx (p₁ p₂ : Pos) : (p₁ + p₂).byteIdx = p₁.byteIdx + p₂.byteIdx := rfl

theorem add_eq (p₁ p₂ : Pos) : p₁ + p₂ = ⟨p₁.byteIdx + p₂.byteIdx⟩ := rfl

@[simp] theorem sub_byteIdx (p₁ p₂ : Pos) : (p₁ - p₂).byteIdx = p₁.byteIdx - p₂.byteIdx := rfl

theorem sub_eq (p₁ p₂ : Pos) : p₁ - p₂ = ⟨p₁.byteIdx - p₂.byteIdx⟩ := rfl

@[simp] theorem addChar_byteIdx (p : Pos) (c : Char) : (p + c).byteIdx = p.byteIdx + csize c := rfl

theorem addChar_eq (p : Pos) (c : Char) : p + c = ⟨p.byteIdx + csize c⟩ := rfl

theorem zero_addChar_byteIdx (c : Char) : ((0 : Pos) + c).byteIdx = csize c := by
  simp only [addChar_byteIdx, byteIdx_zero, Nat.zero_add]

theorem zero_addChar_eq (c : Char) : (0 : Pos) + c = ⟨csize c⟩ := by rw [← zero_addChar_byteIdx]

theorem addChar_right_comm (p : Pos) (c₁ c₂ : Char) : p + c₁ + c₂ = p + c₂ + c₁ := by
  apply ext
  repeat rw [pos_add_char]
  apply Nat.add_right_comm

theorem lt_addChar (p : Pos) (c : Char) : p < p + c := Nat.lt_add_of_pos_right (csize_pos _)

theorem ne_of_lt {i₁ i₂ : Pos} (h : i₁ < i₂) : i₁ ≠ i₂ := mt ext_iff.1 (Nat.ne_of_lt h)

theorem ne_of_gt {i₁ i₂ : Pos} (h : i₁ < i₂) : i₂ ≠ i₁ := (ne_of_lt h).symm

@[simp] theorem addString_byteIdx (p : Pos) (s : String) :
    (p + s).byteIdx = p.byteIdx + s.utf8ByteSize := rfl

theorem addString_eq (p : Pos) (s : String) : p + s = ⟨p.byteIdx + s.utf8ByteSize⟩ := rfl

theorem zero_addString_byteIdx (s : String) : ((0 : Pos) + s).byteIdx = s.utf8ByteSize := by
  simp only [addString_byteIdx, byteIdx_zero, Nat.zero_add]

theorem zero_addString_eq (s : String) : (0 : Pos) + s = ⟨s.utf8ByteSize⟩ := by
  rw [← zero_addString_byteIdx]

theorem le_iff {i₁ i₂ : Pos} : i₁ ≤ i₂ ↔ i₁.byteIdx ≤ i₂.byteIdx := ⟨id, id⟩

theorem lt_iff {i₁ i₂ : Pos} : i₁ < i₂ ↔ i₁.byteIdx < i₂.byteIdx := ⟨id, id⟩

end Pos

private theorem add_csize_pos : 0 < i + csize c :=
  Nat.add_pos_right _ (csize_pos c)

private theorem ne_add_csize_add_self : i ≠ n + csize c + i :=
  Nat.ne_of_lt (Nat.lt_add_of_pos_left add_csize_pos)

private theorem Pos.zero_ne_addChar {i : Pos} {c : Char} : 0 ≠ i + c :=
  Pos.ne_of_lt add_csize_pos

/-- The UTF-8 byte length of a list of characters. (This is intended for specification purposes.) -/
@[inline] def utf8Len : List Char → Nat := utf8ByteSize.go

@[simp] theorem utf8Len_nil : utf8Len [] = 0 := rfl

@[simp] theorem utf8Len_cons : utf8Len (c :: cs) = utf8Len cs + csize c := rfl

@[simp] theorem endPos_eq (cs : List Char) : endPos ⟨cs⟩ = ⟨utf8Len cs⟩ := rfl

/--
Induction along the valid positions in a list of characters.
(This definition is intended only for specification purposes.)
-/
def utf8InductionOn {motive : List Char → Pos → Sort u}
    (s : List Char) (i p : Pos)
    (nil : ∀ i, motive [] i)
    (eq  : ∀ c cs, motive (c :: cs) p)
    (ind : ∀ (c : Char) cs i, i ≠ p → motive cs (i + c) → motive (c :: cs) i) :
    motive s i :=
  match s with
  | [] => nil i
  | c::cs =>
    if h : i = p then
      h ▸ eq c cs
    else ind c cs i h (utf8InductionOn cs (i + c) p nil eq ind)

theorem utf8GetAux_add_right_cancel (s : List Char) (i p n : Nat) :
    utf8GetAux s ⟨i + n⟩ ⟨p + n⟩ = utf8GetAux s ⟨i⟩ ⟨p⟩ := by
  apply utf8InductionOn s ⟨i⟩ ⟨p⟩ (motive := fun s i =>
    utf8GetAux s ⟨i.byteIdx + n⟩ ⟨p + n⟩ = utf8GetAux s i ⟨p⟩) <;>
  simp [utf8GetAux]
  intro c cs ⟨i⟩ h ih
  simp [Pos.ext_iff, Pos.addChar_eq] at h ⊢
  simp [Nat.add_right_cancel_iff, h]
  rw [Nat.add_right_comm]
  exact ih

theorem utf8GetAux_addChar_right_cancel (s : List Char) (i p : Pos) (c : Char) :
    utf8GetAux s (i + c) (p + c) = utf8GetAux s i p := utf8GetAux_add_right_cancel ..

theorem get_cons_addChar (c : Char) (cs : List Char) (i : Pos) :
    get ⟨c :: cs⟩ (i + c) = get ⟨cs⟩ i := by
  simp [get, utf8GetAux, Pos.zero_ne_addChar, utf8GetAux_addChar_right_cancel]

theorem extract.go₂_add_right_cancel (s : List Char) (i e n : Nat) :
    go₂ s ⟨i + n⟩ ⟨e + n⟩ = go₂ s ⟨i⟩ ⟨e⟩ := by
  apply utf8InductionOn s ⟨i⟩ ⟨e⟩ (motive := fun s i =>
    go₂ s ⟨i.byteIdx + n⟩ ⟨e + n⟩ = go₂ s i ⟨e⟩) <;> simp [go₂]
  intro c cs ⟨i⟩ h ih
  simp [Pos.ext_iff, Pos.addChar_eq] at h ⊢
  simp [Nat.add_right_cancel_iff, h]
  rw [Nat.add_right_comm]
  exact ih

theorem extract.go₂_append_left : ∀ (s t : List Char) (i e : Nat),
    e = utf8Len s + i → go₂ (s ++ t) ⟨i⟩ ⟨e⟩ = s
| [], t, i, _, rfl => by cases t <;> simp [go₂]
| c :: cs, t, i, _, rfl => by
  simp [go₂, Pos.ext_iff, ne_add_csize_add_self, Pos.addChar_eq]
  apply go₂_append_left; rw [Nat.add_right_comm, Nat.add_assoc]

theorem extract.go₁_add_right_cancel (s : List Char) (i b e n : Nat) :
    go₁ s ⟨i + n⟩ ⟨b + n⟩ ⟨e + n⟩ = go₁ s ⟨i⟩ ⟨b⟩ ⟨e⟩ := by
  apply utf8InductionOn s ⟨i⟩ ⟨b⟩ (motive := fun s i =>
    go₁ s ⟨i.byteIdx + n⟩ ⟨b + n⟩ ⟨e + n⟩ = go₁ s i ⟨b⟩ ⟨e⟩) <;>
  simp [go₁]
  · intro c cs
    apply go₂_add_right_cancel
  · intro c cs ⟨i⟩ h ih
    simp [Pos.ext_iff, Pos.addChar_eq] at h ih ⊢
    simp [Nat.add_right_cancel_iff, h]
    rw [Nat.add_right_comm]
    exact ih

theorem extract.go₁_cons_addChar (c : Char) (cs : List Char) (b e : Pos) :
    go₁ (c :: cs) 0 (b + c) (e + c) = go₁ cs 0 b e := by
  simp [go₁, Pos.ext_iff, Nat.ne_of_lt add_csize_pos]
  apply go₁_add_right_cancel

theorem extract.go₁_append_right : ∀ (s t : List Char) (i b : Nat) (e : Pos),
    b = utf8Len s + i → go₁ (s ++ t) ⟨i⟩ ⟨b⟩ e = go₂ t ⟨b⟩ e
| [], t, i, _, e, rfl => by cases t <;> simp [go₁, go₂]
| c :: cs, t, i, _, e, rfl => by
  simp [go₁, Pos.ext_iff, ne_add_csize_add_self, Pos.addChar_eq]
  apply go₁_append_right; rw [Nat.add_right_comm, Nat.add_assoc]

theorem extract.go₁_zero_utf8Len (s : List Char) : go₁ s 0 0 ⟨utf8Len s⟩ = s :=
  (go₁_append_right [] s 0 0 ⟨utf8Len s⟩ rfl).trans <| by
    simpa using go₂_append_left s [] 0 (utf8Len s) rfl

theorem extract_cons_addChar (c : Char) (cs : List Char) (b e : Pos) :
    extract ⟨c :: cs⟩ (b + c) (e + c) = extract ⟨cs⟩ b e := by
  simp [extract, Nat.add_le_add_iff_le_right]
  split <;> [rfl, rw [extract.go₁_cons_addChar]]

theorem extract_zero_endPos : ∀ (s : String), s.extract 0 (endPos s) = s
| ⟨[]⟩ => rfl
| ⟨c :: cs⟩ => by
  simp [extract, Nat.ne_of_gt add_csize_pos]; congr
  apply extract.go₁_zero_utf8Len

theorem Iterator.hasNext_cons_add_csize (c : Char) (cs : List Char) (i : Pos) :
    hasNext ⟨⟨c :: cs⟩, i + c⟩ = hasNext ⟨⟨cs⟩, i⟩ := by
  simp [hasNext, Nat.add_lt_add_iff_lt_right]

@[simp] theorem toString_toSubstring (s : String) : s.toSubstring.toString = s :=
  extract_zero_endPos _

end String

open String

namespace Substring

theorem next_cons_zero (c : Char) (cs : List Char) :
    next ⟨⟨c :: cs⟩, 0, ⟨utf8Len cs + csize c⟩⟩ 0 = ⟨csize c⟩ := by
  simp [next, Pos.ext_iff, Nat.ne_of_lt add_csize_pos, String.next]; rfl

theorem next_cons_addChar (c : Char) (cs : List Char) (p : Pos) :
    next ⟨⟨c :: cs⟩, 0, ⟨utf8Len cs + csize c⟩⟩ (p + c) =
    next ⟨⟨cs⟩, 0, ⟨utf8Len cs⟩⟩ p + c := by
  simp [next, Pos.add_eq, Pos.ext_iff, Nat.add_right_cancel_iff]
  split
  · next h => simp [h]
  · simp [String.next]
    rw [← Pos.addChar_eq, get_cons_addChar]
    apply Nat.add_right_comm

/--
Induction on `Substring.nextn`.
-/
def nextn.inductionOn.{u} {motive : Nat → Pos → Sort u}
    (ss : Substring) (i : Nat) (p : Pos)
    (zero : ∀ p, motive 0 p)
    (ind  : ∀ i p, motive i (ss.next p) → motive (i + 1) p) :
    motive i p :=
  match i with
  | 0   => zero p
  | i+1 => ind i p (inductionOn ss i (ss.next p) zero ind)

theorem nextn_next_eq (ss : Substring) (i : Nat) (p : Pos) :
    ss.nextn i (next ss p) = ss.next (ss.nextn i p) := by
  apply nextn.inductionOn ss i p (motive := fun i p =>
    ss.nextn i (next ss p) = ss.next (ss.nextn i p)) <;>
  simp [nextn, next]

theorem nextn_cons_addChar (c : Char) (cs : List Char) (i : Nat) (p : Pos) :
    nextn ⟨⟨c :: cs⟩, 0, ⟨utf8Len cs + csize c⟩⟩ i (p + c) =
    nextn ⟨⟨cs⟩, 0, ⟨utf8Len cs⟩⟩ i p + c := by
  induction i with
  | zero => rfl
  | succ i ih =>
    simp only [nextn]; rw [nextn_next_eq, nextn_next_eq, ih]
    apply next_cons_addChar

end Substring

namespace String

attribute [simp] toList -- prefer `String.data` over `String.toList` in lemmas

@[simp] theorem drop_empty {n : Nat} : "".drop n = "" := by induction n <;> [rfl, assumption]

theorem drop_cons_succ (c : Char) (cs : List Char) (n : Nat) :
    drop ⟨c :: cs⟩ n.succ = drop ⟨cs⟩ n := by
  simp [drop, Substring.toString, Substring.drop, toSubstring, Substring.nextn,
    Substring.next_cons_zero, Pos.add_eq]
  rw [← Pos.zero_addChar_eq, Substring.nextn_cons_addChar]
  apply extract_cons_addChar

theorem drop_eq : ∀ (s : String) (n : Nat), drop s n = ⟨s.data.drop n⟩
| ⟨s⟩, n => by
  induction n generalizing s with
  | zero => exact toString_toSubstring ⟨s⟩
  | succ n ih =>
    match s with
    | [] => exact drop_empty
    | c::cs => simp [drop_cons_succ]; exact ih cs

end String

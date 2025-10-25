/-
Copyright (c) 2023 Bulhwi Cha. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bulhwi Cha, Mario Carneiro
-/
module

public import Batteries.Data.String.Basic
public import Batteries.Tactic.Lint.Misc
public import Batteries.Tactic.SeqFocus
public import Batteries.Classes.Order
public import Batteries.Data.List.Basic
import all Init.Data.String.Defs  -- for unfolding `isEmpty`
import all Init.Data.String.Substring  -- for unfolding `Substring` functions
import all Init.Data.String.Iterator  -- for unfolding `Iterator` functions
import all Init.Data.String.Extra  -- for unfolding `Substring.toIterator`
import all Init.Data.String.TakeDrop  -- for unfolding `drop`
import all Init.Data.String.Modify  -- for unfolding `String.mapAux`

@[expose] public section

namespace String

-- TODO(kmill): add `@[ext]` attribute to `String.ext` in core.
attribute [ext (iff := false)] ext

theorem lt_antisymm {s₁ s₂ : String} (h₁ : ¬s₁ < s₂) (h₂ : ¬s₂ < s₁) : s₁ = s₂ := by
  simp at h₁ h₂
  exact String.le_antisymm h₂ h₁

instance : Std.LawfulLTOrd String :=
  .compareOfLessAndEq_of_irrefl_of_trans_of_antisymm
    String.lt_irrefl String.lt_trans String.lt_antisymm

theorem mk_length (s : List Char) : (String.mk s).length = s.length := by
  simp

attribute [simp] toList -- prefer `String.data` over `String.toList` in lemmas

theorem Pos.Raw.offsetBy_eq {p q : Pos.Raw} : p.offsetBy q = ⟨q.byteIdx + p.byteIdx⟩ := by
  ext
  simp

private theorem add_utf8Size_pos : 0 < i + Char.utf8Size c :=
  Nat.add_pos_right _ (Char.utf8Size_pos c)

private theorem ne_add_utf8Size_add_self : i ≠ n + Char.utf8Size c + i :=
  Nat.ne_of_lt (Nat.lt_add_of_pos_left add_utf8Size_pos)

private theorem ne_self_add_add_utf8Size : i ≠ i + (n + Char.utf8Size c) :=
  Nat.ne_of_lt (Nat.lt_add_of_pos_right add_utf8Size_pos)

/-- The UTF-8 byte length of a list of characters. (This is intended for specification purposes.) -/
@[inline] def utf8Len : List Char → Nat
  | []    => 0
  | c::cs => utf8Len cs + c.utf8Size

theorem utf8ByteSize_mk (cs) : utf8ByteSize (String.mk cs) = utf8Len cs := by
  induction cs with
  | nil => simp [utf8Len]
  | cons c cs ih =>
    rw [String.mk_eq_asString, utf8Len, ← ih, ← List.singleton_append, List.asString_append,
      utf8ByteSize_append, Nat.add_comm]
    congr
    rw [← size_bytes, List.bytes_asString, List.utf8Encode_singleton,
      List.size_toByteArray, length_utf8EncodeChar]

@[simp] theorem utf8Len_nil : utf8Len [] = 0 := rfl

@[simp] theorem utf8Len_cons (c cs) : utf8Len (c :: cs) = utf8Len cs + c.utf8Size := rfl

@[simp] theorem utf8Len_append (cs₁ cs₂) : utf8Len (cs₁ ++ cs₂) = utf8Len cs₁ + utf8Len cs₂ := by
  induction cs₁ <;> simp [*, Nat.add_right_comm]

theorem utf8Len_reverseAux (cs₁ cs₂) :
    utf8Len (cs₁.reverseAux cs₂) = utf8Len cs₁ + utf8Len cs₂ := by
  induction cs₁ generalizing cs₂ <;> simp_all [← Nat.add_assoc, Nat.add_right_comm]

@[simp] theorem utf8Len_reverse (cs) : utf8Len cs.reverse = utf8Len cs := utf8Len_reverseAux ..

@[simp] theorem utf8Len_eq_zero : utf8Len l = 0 ↔ l = [] := by
  cases l <;> simp [Nat.ne_zero_iff_zero_lt.mpr (Char.utf8Size_pos _)]

section
open List
theorem utf8Len_le_of_sublist : ∀ {cs₁ cs₂}, cs₁ <+ cs₂ → utf8Len cs₁ ≤ utf8Len cs₂
  | _, _, .slnil => Nat.le_refl _
  | _, _, .cons _ h => Nat.le_trans (utf8Len_le_of_sublist h) (Nat.le_add_right ..)
  | _, _, .cons₂ _ h => Nat.add_le_add_right (utf8Len_le_of_sublist h) _

theorem utf8Len_le_of_infix (h : cs₁ <:+: cs₂) : utf8Len cs₁ ≤ utf8Len cs₂ :=
  utf8Len_le_of_sublist h.sublist

theorem utf8Len_le_of_suffix (h : cs₁ <:+ cs₂) : utf8Len cs₁ ≤ utf8Len cs₂ :=
  utf8Len_le_of_sublist h.sublist

theorem utf8Len_le_of_prefix (h : cs₁ <+: cs₂) : utf8Len cs₁ ≤ utf8Len cs₂ :=
  utf8Len_le_of_sublist h.sublist
end

@[simp] theorem rawEndPos_asString (cs : List Char) : rawEndPos cs.asString = ⟨utf8Len cs⟩ := by
  apply Pos.Raw.ext
  simp [String.rawEndPos, ← String.mk_eq_asString, utf8ByteSize_mk]

@[deprecated rawEndPos_asString (since := "2025-10-21")]
theorem endPos_asString (cs : List Char) : rawEndPos cs.asString = ⟨utf8Len cs⟩ :=
  rawEndPos_asString cs

theorem rawEndPos_mk (cs : List Char) : rawEndPos (mk cs) = ⟨utf8Len cs⟩ := by
  simp

@[deprecated rawEndPos_mk (since := "2025-10-21")]
theorem endPos_mk (cs : List Char) : rawEndPos (mk cs) = ⟨utf8Len cs⟩ :=
  rawEndPos_mk cs

@[simp]
theorem utf8Len_data (s : String) : utf8Len s.data = s.utf8ByteSize := by
  rw [← utf8ByteSize_mk, String.mk_eq_asString, asString_data]

namespace Pos.Raw

-- TODO(kmill): add `@[ext]` attribute to `String.Pos.ext` in core.
attribute [ext (iff := false)] ext

theorem lt_addChar (p : Pos.Raw) (c : Char) : p < p + c :=
  Nat.lt_add_of_pos_right (Char.utf8Size_pos _)

private theorem zero_ne_addChar {i : Pos.Raw} {c : Char} : 0 ≠ i + c :=
  ne_of_lt add_utf8Size_pos

/-- A string position is valid if it is equal to the UTF-8 length of an initial substring of `s`. -/
inductive Valid : String → Pos.Raw → Prop where
  /--
  A string position is valid if it is equal to the UTF-8 length of an initial substring of `s`.
  -/
  | mk (cs cs' : List Char) {p} (hp : p.1 = utf8Len cs) : Valid (String.mk (cs ++ cs')) p

theorem Valid.intro {s : String} {p : Pos.Raw}
    (h : ∃ cs cs', cs ++ cs' = s.data ∧ p.1 = utf8Len cs) : Valid s p := by
  obtain ⟨cs, cs', h₁, h₂⟩ := h
  rw [← String.asString_data (b := s), ← h₁]
  exact .mk cs cs' h₂

theorem Valid.exists : {s : String} → {p : Pos.Raw} → Valid s p →
    ∃ cs cs', String.mk (cs ++ cs') = s ∧ p = ⟨utf8Len cs⟩
  | _, _, .mk cs cs' rfl => ⟨cs, cs', rfl, rfl⟩

@[simp] theorem valid_zero : Valid s 0 := .intro ⟨[], s.data, rfl, rfl⟩

@[simp] theorem valid_rawEndPos : Valid s (rawEndPos s) :=
  .intro ⟨s.data, [], by simp, by simp [rawEndPos]⟩

@[deprecated valid_rawEndPos (since := "2025-10-21")]
theorem valid_endPos : Valid s (rawEndPos s) :=
  valid_rawEndPos

theorem Valid.le_rawEndPos : ∀ {s p}, Valid s p → p ≤ rawEndPos s
  | _, ⟨_⟩, .mk cs cs' rfl => by simp [rawEndPos, le_iff, -String.mk_eq_asString, utf8ByteSize_mk]

@[deprecated le_rawEndPos (since := "2025-10-21")]
theorem Valid.le_endPos : ∀ {s p}, Valid s p → p ≤ rawEndPos s :=
  le_rawEndPos

end Pos.Raw

@[deprecated rawEndPos_eq_zero_iff (since := "2025-10-21")]
theorem endPos_eq_zero (s : String) : rawEndPos s = 0 ↔ s = "" :=
  rawEndPos_eq_zero_iff

theorem isEmpty_iff (s : String) : isEmpty s ↔ s = "" := by
  simp [isEmpty]

/--
Induction along the valid positions in a list of characters.
(This definition is intended only for specification purposes.)
-/
def utf8InductionOn {motive : List Char → Pos.Raw → Sort u}
    (s : List Char) (i p : Pos.Raw)
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
    Pos.Raw.utf8GetAux s ⟨i + n⟩ ⟨p + n⟩ = Pos.Raw.utf8GetAux s ⟨i⟩ ⟨p⟩ := by
  apply utf8InductionOn s ⟨i⟩ ⟨p⟩ (motive := fun s i =>
    Pos.Raw.utf8GetAux s ⟨i.byteIdx + n⟩ ⟨p + n⟩ = Pos.Raw.utf8GetAux s i ⟨p⟩) <;>
  simp only [Pos.Raw.utf8GetAux, Char.reduceDefault, implies_true, ↓reduceIte, ne_eq,
    Pos.Raw.byteIdx_add_char]
  intro c cs ⟨i⟩ h ih
  simp only [Pos.Raw.ext_iff, Pos.Raw.add_char_eq] at h ⊢
  simp only [Nat.add_right_cancel_iff, h, ↓reduceIte]
  rw [Nat.add_right_comm]
  exact ih

theorem utf8GetAux_addChar_right_cancel (s : List Char) (i p : Pos.Raw) (c : Char) :
    Pos.Raw.utf8GetAux s (i + c) (p + c) = Pos.Raw.utf8GetAux s i p :=
  utf8GetAux_add_right_cancel ..

theorem utf8GetAux_of_valid (cs cs' : List Char) {i p : Nat} (hp : i + utf8Len cs = p) :
    Pos.Raw.utf8GetAux (cs ++ cs') ⟨i⟩ ⟨p⟩ = cs'.headD default := by
  match cs, cs' with
  | [], [] => rfl
  | [], c::cs' => simp [← hp, Pos.Raw.utf8GetAux]
  | c::cs, cs' =>
    simp only [List.cons_append, Pos.Raw.utf8GetAux, Char.reduceDefault]
    rw [if_neg]
    case hnc => simp only [← hp, utf8Len_cons, Pos.Raw.ext_iff]; exact ne_self_add_add_utf8Size
    refine utf8GetAux_of_valid cs cs' ?_
    simpa [Nat.add_assoc, Nat.add_comm] using hp

theorem get_of_valid (cs cs' : List Char) :
    Pos.Raw.get (mk (cs ++ cs')) ⟨utf8Len cs⟩ = cs'.headD default := by
  rw [Pos.Raw.get, String.mk_eq_asString, List.data_asString]
  exact utf8GetAux_of_valid _ _ (Nat.zero_add _)

theorem get_cons_addChar (c : Char) (cs : List Char) (i : Pos.Raw) :
    (i + c).get (c :: cs).asString = i.get cs.asString := by
  simp [Pos.Raw.get, Pos.Raw.utf8GetAux, Pos.Raw.zero_ne_addChar, utf8GetAux_addChar_right_cancel]

theorem utf8GetAux?_of_valid (cs cs' : List Char) {i p : Nat} (hp : i + utf8Len cs = p) :
    Pos.Raw.utf8GetAux? (cs ++ cs') ⟨i⟩ ⟨p⟩ = cs'.head? := by
  match cs, cs' with
  | [], [] => rfl
  | [], c::cs' => simp [← hp, Pos.Raw.utf8GetAux?]
  | c::cs, cs' =>
    simp only [List.cons_append, Pos.Raw.utf8GetAux?]
    rw [if_neg]
    case hnc => simp only [← hp, Pos.Raw.ext_iff]; exact ne_self_add_add_utf8Size
    refine utf8GetAux?_of_valid cs cs' ?_
    simpa [Nat.add_assoc, Nat.add_comm] using hp

theorem get?_of_valid (cs cs' : List Char) :
    Pos.Raw.get? (cs ++ cs').asString ⟨utf8Len cs⟩ = cs'.head? := by
  rw [Pos.Raw.get?, List.data_asString]
  exact utf8GetAux?_of_valid _ _ (Nat.zero_add _)

theorem utf8SetAux_of_valid (c' : Char) (cs cs' : List Char) {i p : Nat} (hp : i + utf8Len cs = p) :
    Pos.Raw.utf8SetAux c' (cs ++ cs') ⟨i⟩ ⟨p⟩ = cs ++ cs'.modifyHead fun _ => c' := by
  match cs, cs' with
  | [], [] => rfl
  | [], c::cs' => simp [← hp, Pos.Raw.utf8SetAux]
  | c::cs, cs' =>
    simp only [Pos.Raw.utf8SetAux, List.cons_append]
    rw [if_neg]
    case hnc => simp only [← hp, Pos.Raw.ext_iff]; exact ne_self_add_add_utf8Size
    refine congrArg (c::·) (utf8SetAux_of_valid c' cs cs' ?_)
    simpa [Nat.add_assoc, Nat.add_comm] using hp

theorem set_of_valid (cs cs' : List Char) (c' : Char) :
    Pos.Raw.set (mk (cs ++ cs')) ⟨utf8Len cs⟩ c' =
      (cs ++ cs'.modifyHead fun _ => c').asString := by
  ext
  rw [Pos.Raw.set, List.data_asString, List.data_asString, String.mk_eq_asString,
    List.data_asString, utf8SetAux_of_valid _ _ _]
  exact Nat.zero_add _

theorem modify_of_valid (cs cs' : List Char) :
    Pos.Raw.modify (mk (cs ++ cs')) ⟨utf8Len cs⟩ f = (cs ++ cs'.modifyHead f).asString := by
  rw [Pos.Raw.modify, set_of_valid, get_of_valid]; cases cs' <;> rfl

theorem next_of_valid' (cs cs' : List Char) :
    Pos.Raw.next (mk (cs ++ cs')) ⟨utf8Len cs⟩ = ⟨utf8Len cs + (cs'.headD default).utf8Size⟩ := by
  simp only [Pos.Raw.next, get_of_valid]; rfl

theorem next_of_valid (cs : List Char) (c : Char) (cs' : List Char) :
    Pos.Raw.next (mk (cs ++ c :: cs')) ⟨utf8Len cs⟩ = ⟨utf8Len cs + c.utf8Size⟩ := next_of_valid' ..

@[simp] theorem atEnd_iff (s : String) (p : Pos.Raw) : p.atEnd s ↔ s.rawEndPos ≤ p :=
  decide_eq_true_iff

theorem valid_next {p : Pos.Raw} (h : p.Valid s) (h₂ : p < s.rawEndPos) :
    (Pos.Raw.next s p).Valid s := by
  match s, p, h with
  | _, ⟨_⟩, .mk cs [] rfl => simp at h₂
  | _, ⟨_⟩, .mk cs (c::cs') rfl =>
    rw [next_of_valid]
    simpa using Pos.Raw.Valid.mk (cs ++ [c]) cs' rfl

theorem utf8PrevAux_of_valid {cs cs' : List Char} {c : Char} {i p : Nat}
    (hp : i + (utf8Len cs + c.utf8Size) = p) :
    Pos.Raw.utf8PrevAux (cs ++ c :: cs') ⟨i⟩ ⟨p⟩ = ⟨i + utf8Len cs⟩ := by
  match cs with
  | [] => simp [Pos.Raw.utf8PrevAux, ← hp, Pos.Raw.add_char_eq]
  | c'::cs =>
    simp only [Pos.Raw.utf8PrevAux, List.cons_append, utf8Len_cons, ← hp]
    rw [if_neg]
    case hnc =>
      simp only [Pos.Raw.le_iff, Pos.Raw.byteIdx_add_char]
      grind [!Char.utf8Size_pos]
    refine (utf8PrevAux_of_valid (by simp [Nat.add_assoc, Nat.add_left_comm])).trans ?_
    simp [Nat.add_assoc, Nat.add_comm]

theorem prev_of_valid (cs : List Char) (c : Char) (cs' : List Char) :
    Pos.Raw.prev (mk (cs ++ c :: cs')) ⟨utf8Len cs + c.utf8Size⟩ = ⟨utf8Len cs⟩ := by
  simp only [Pos.Raw.prev, String.mk_eq_asString, List.data_asString]
  rw [utf8PrevAux_of_valid] <;> simp

theorem prev_of_valid' (cs cs' : List Char) :
    Pos.Raw.prev (mk (cs ++ cs')) ⟨utf8Len cs⟩ = ⟨utf8Len cs.dropLast⟩ := by
  match cs, cs.eq_nil_or_concat with
  | _, .inl rfl => apply Pos.Raw.prev_zero
  | _, .inr ⟨cs, c, rfl⟩ => simp [-String.mk_eq_asString, prev_of_valid]

theorem front_eq (s : String) : front s = s.data.headD default := by
  unfold front; simpa using get_of_valid [] s.data

theorem back_eq (s : String) : back s = s.data.getLastD default := by
  conv => lhs; rw [← s.asString_data]
  match s.data.eq_nil_or_concat with
  | .inl h => simp [h]; rfl
  | .inr ⟨cs, c, h⟩ =>
    simp only [h, back_eq_get_prev_rawEndPos]
    have : (mk (cs ++ [c])).rawEndPos = ⟨utf8Len cs + c.utf8Size⟩ := by
      simp [-String.mk_eq_asString, rawEndPos, utf8ByteSize_mk]
    simp [← String.mk_eq_asString, this, prev_of_valid, get_of_valid]

theorem atEnd_of_valid (cs : List Char) (cs' : List Char) :
    String.Pos.Raw.atEnd (mk (cs ++ cs')) ⟨utf8Len cs⟩ ↔ cs' = [] := by
  rw [atEnd_iff]
  cases cs' <;> simp [-String.mk_eq_asString, add_utf8Size_pos, rawEndPos, utf8ByteSize_mk]

unseal posOfAux findAux in
theorem posOfAux_eq (s c) : posOfAux s c = findAux s (· == c) := (rfl)

unseal posOfAux findAux in
theorem posOf_eq (s c) : posOf s c = find s (· == c) := (rfl)

unseal revPosOfAux revFindAux in
theorem revPosOfAux_eq (s c) : revPosOfAux s c = revFindAux s (· == c) := (rfl)

unseal revPosOfAux revFindAux in
theorem revPosOf_eq (s c) : revPosOf s c = revFind s (· == c) := (rfl)

@[nolint unusedHavesSuffices] -- false positive from unfolding String.findAux
theorem findAux_of_valid (p) : ∀ l m r,
    findAux (mk (l ++ m ++ r)) p ⟨utf8Len l + utf8Len m⟩ ⟨utf8Len l⟩ =
    ⟨utf8Len l + utf8Len (m.takeWhile (!p ·))⟩
  | l, [], r => by unfold findAux List.takeWhile; simp
  | l, c::m, r => by
    unfold findAux List.takeWhile
    rw [dif_pos (by exact Nat.lt_add_of_pos_right add_utf8Size_pos)]
    have h1 := get_of_valid l (c::m++r); have h2 := next_of_valid l c (m++r)
    simp only [List.cons_append, Char.reduceDefault, List.headD_cons] at h1 h2
    simp only [List.append_assoc, List.cons_append, h1, utf8Len_cons, h2]
    cases p c
    · simp only [Bool.false_eq_true, ↓reduceIte, Bool.not_false, utf8Len_cons]
      have foo := findAux_of_valid p (l++[c]) m r
      simp only [List.append_assoc, List.cons_append, utf8Len_append,
        utf8Len_cons, utf8Len_nil, Nat.zero_add, List.nil_append] at foo
      rw [Nat.add_right_comm, Nat.add_assoc] at foo
      rw [foo, Nat.add_right_comm, Nat.add_assoc]
    · simp

theorem find_of_valid (p s) : find s p = ⟨utf8Len (s.data.takeWhile (!p ·))⟩ := by
  simpa using findAux_of_valid p [] s.data []

@[nolint unusedHavesSuffices] -- false positive from unfolding String.revFindAux
theorem revFindAux_of_valid (p) : ∀ l r,
    revFindAux (mk (l.reverse ++ r)) p ⟨utf8Len l⟩ = (l.dropWhile (!p ·)).tail?.map (⟨utf8Len ·⟩)
  | [], r => by unfold revFindAux List.dropWhile; simp
  | c::l, r => by
    unfold revFindAux List.dropWhile
    rw [dif_neg (by exact Pos.Raw.ne_of_gt add_utf8Size_pos)]
    have h1 := get_of_valid l.reverse (c::r); have h2 := prev_of_valid l.reverse c r
    simp only [utf8Len_reverse, Char.reduceDefault, List.headD_cons] at h1 h2
    simp only [List.reverse_cons, List.append_assoc, List.singleton_append,
      utf8Len_cons, h2, h1]
    cases p c <;> simp only [Bool.false_eq_true, ↓reduceIte, Bool.not_false, Bool.not_true,
      List.tail?_cons, Option.map_some]
    exact revFindAux_of_valid p l (c::r)

theorem revFind_of_valid (p s) :
    revFind s p = (s.data.reverse.dropWhile (!p ·)).tail?.map (⟨utf8Len ·⟩) := by
  simpa using revFindAux_of_valid p s.data.reverse []

theorem firstDiffPos_loop_eq (l₁ l₂ r₁ r₂ stop p)
    (hl₁ : p = utf8Len l₁) (hl₂ : p = utf8Len l₂)
    (hstop : stop = min (utf8Len l₁ + utf8Len r₁) (utf8Len l₂ + utf8Len r₂)) :
    firstDiffPos.loop (mk (l₁ ++ r₁)) (mk (l₂ ++ r₂)) ⟨stop⟩ ⟨p⟩ =
      ⟨p + utf8Len (List.takeWhile₂ (· = ·) r₁ r₂).1⟩ := by
  unfold List.takeWhile₂; split <;> unfold firstDiffPos.loop
  · next a r₁ b r₂ =>
    rw [
      dif_pos <| by
        rw [hstop, ← hl₁, ← hl₂]
        refine Nat.lt_min.2 ⟨?_, ?_⟩ <;> exact Nat.lt_add_of_pos_right add_utf8Size_pos,
      show Pos.Raw.get (mk (l₁ ++ a :: r₁)) ⟨p⟩ = a by
        simp [hl₁, -String.mk_eq_asString, get_of_valid],
      show Pos.Raw.get (mk (l₂ ++ b :: r₂)) ⟨p⟩ = b by
        simp [hl₂, -String.mk_eq_asString, get_of_valid]]
    simp only [bne_iff_ne, ne_eq, ite_not, decide_eq_true_eq]
    split
    · simp only [utf8Len_cons]
      subst b
      rw [show Pos.Raw.next (mk (l₁ ++ a :: r₁)) ⟨p⟩ = ⟨utf8Len l₁ + a.utf8Size⟩ by
        simp [hl₁, -String.mk_eq_asString, next_of_valid]]
      simpa [← hl₁, ← Nat.add_assoc, Nat.add_right_comm] using
        firstDiffPos_loop_eq (l₁ ++ [a]) (l₂ ++ [a]) r₁ r₂ stop (p + a.utf8Size)
          (by simp [hl₁]) (by simp [hl₂]) (by simp [hstop, ← Nat.add_assoc, Nat.add_right_comm])
    · simp
  · next h =>
    rw [dif_neg] <;> simp [hstop, ← hl₁, ← hl₂, -Nat.not_lt, Nat.lt_min]
    intro h₁ h₂
    have : ∀ {cs}, 0 < utf8Len cs → cs ≠ [] := by rintro _ h rfl; simp at h
    obtain ⟨a, as, e₁⟩ := List.exists_cons_of_ne_nil (this h₁)
    obtain ⟨b, bs, e₂⟩ := List.exists_cons_of_ne_nil (this h₂)
    exact h _ _ _ _ e₁ e₂

theorem firstDiffPos_eq (a b : String) :
    firstDiffPos a b = ⟨utf8Len (List.takeWhile₂ (· = ·) a.data b.data).1⟩ := by
  simpa [firstDiffPos] using
    firstDiffPos_loop_eq [] [] a.data b.data
      ((utf8Len a.data).min (utf8Len b.data)) 0 rfl rfl (by simp)

theorem Pos.Raw.extract.go₂_add_right_cancel (s : List Char) (i e n : Nat) :
    go₂ s ⟨i + n⟩ ⟨e + n⟩ = go₂ s ⟨i⟩ ⟨e⟩ := by
  apply utf8InductionOn s ⟨i⟩ ⟨e⟩ (motive := fun s i =>
    go₂ s ⟨i.byteIdx + n⟩ ⟨e + n⟩ = go₂ s i ⟨e⟩)
    <;> simp only [ne_eq, go₂, Pos.Raw.byteIdx_add_char, implies_true, ↓reduceIte]
  intro c cs ⟨i⟩ h ih
  simp only [Pos.Raw.ext_iff, Pos.Raw.add_char_eq] at h ⊢
  simp only [Nat.add_right_cancel_iff, h, ↓reduceIte, List.cons.injEq, true_and]
  rw [Nat.add_right_comm]
  exact ih

theorem Pos.Raw.extract.go₂_append_left : ∀ (s t : List Char) (i e : Nat),
    e = utf8Len s + i → go₂ (s ++ t) ⟨i⟩ ⟨e⟩ = s
| [], t, i, _, rfl => by cases t <;> simp [go₂]
| c :: cs, t, i, _, rfl => by
  simp only [List.cons_append, utf8Len_cons, go₂, Pos.Raw.ext_iff, ne_add_utf8Size_add_self,
    ↓reduceIte, Pos.Raw.add_char_eq, List.cons.injEq, true_and]
  apply go₂_append_left; rw [Nat.add_right_comm, Nat.add_assoc]

theorem Pos.Raw.extract.go₁_add_right_cancel (s : List Char) (i b e n : Nat) :
    go₁ s ⟨i + n⟩ ⟨b + n⟩ ⟨e + n⟩ = go₁ s ⟨i⟩ ⟨b⟩ ⟨e⟩ := by
  apply utf8InductionOn s ⟨i⟩ ⟨b⟩ (motive := fun s i =>
    go₁ s ⟨i.byteIdx + n⟩ ⟨b + n⟩ ⟨e + n⟩ = go₁ s i ⟨b⟩ ⟨e⟩)
    <;> simp only [ne_eq, go₁, Pos.Raw.byteIdx_add_char, implies_true, ↓reduceIte]
  · intro c cs
    apply go₂_add_right_cancel
  · intro c cs ⟨i⟩ h ih
    simp only [Pos.Raw.ext_iff, Pos.Raw.add_char_eq] at h ih ⊢
    simp only [Nat.add_right_cancel_iff, h, ↓reduceIte]
    rw [Nat.add_right_comm]
    exact ih

theorem Pos.Raw.extract.go₁_cons_addChar (c : Char) (cs : List Char) (b e : Pos.Raw) :
    go₁ (c :: cs) 0 (b + c) (e + c) = go₁ cs 0 b e := by
  simp only [go₁, Pos.Raw.ext_iff, Pos.Raw.byteIdx_zero, byteIdx_add_char,
    Nat.ne_of_lt add_utf8Size_pos, ↓reduceIte]
  apply go₁_add_right_cancel

theorem Pos.Raw.extract.go₁_append_right : ∀ (s t : List Char) (i b : Nat) (e : Pos.Raw),
    b = utf8Len s + i → go₁ (s ++ t) ⟨i⟩ ⟨b⟩ e = go₂ t ⟨b⟩ e
| [], t, i, _, e, rfl => by cases t <;> simp [go₁, go₂]
| c :: cs, t, i, _, e, rfl => by
  simp only [go₁, utf8Len_cons, Pos.Raw.ext_iff, ne_add_utf8Size_add_self, ↓reduceIte,
    List.cons_append, Pos.Raw.add_char_eq]
  apply go₁_append_right; rw [Nat.add_right_comm, Nat.add_assoc]

theorem Pos.Raw.extract.go₁_zero_utf8Len (s : List Char) : go₁ s 0 0 ⟨utf8Len s⟩ = s :=
  (go₁_append_right [] s 0 0 ⟨utf8Len s⟩ rfl).trans <| by
    simpa using go₂_append_left s [] 0 (utf8Len s) rfl

theorem extract_cons_addChar (c : Char) (cs : List Char) (b e : Pos.Raw) :
    Pos.Raw.extract (mk (c :: cs)) (b + c) (e + c) = Pos.Raw.extract (mk cs) b e := by
  simp only [Pos.Raw.extract, Pos.Raw.byteIdx_add_char, ge_iff_le, Nat.add_le_add_iff_right]
  split <;> [rfl; simp [Pos.Raw.extract.go₁_cons_addChar]]

theorem extract_zero_rawEndPos (s : String) : Pos.Raw.extract s 0 (rawEndPos s) = s := by
  obtain ⟨l, rfl⟩ := s.exists_eq_asString
  match l with
  | [] => rfl
  | c :: cs =>
    simp only [Pos.Raw.extract, Pos.Raw.byteIdx_zero, rawEndPos_asString, utf8Len_cons, ge_iff_le,
      Nat.le_zero_eq, Nat.ne_of_gt add_utf8Size_pos, ↓reduceIte, List.data_asString]
    congr
    apply Pos.Raw.extract.go₁_zero_utf8Len

@[deprecated extract_zero_rawEndPos (since := "2025-10-21")]
theorem extract_zero_endPos (s : String) : Pos.Raw.extract s 0 (rawEndPos s) = s :=
  extract_zero_rawEndPos s

theorem extract_of_valid (l m r : List Char) :
    Pos.Raw.extract (mk (l ++ m ++ r)) ⟨utf8Len l⟩ ⟨utf8Len l + utf8Len m⟩ = mk m := by
  simp only [Pos.Raw.extract]
  split
  · next h => rw [utf8Len_eq_zero.1 <| Nat.le_zero.1 <| Nat.add_le_add_iff_left.1 h]
  · congr
    rw [List.append_assoc, String.mk_eq_asString, List.data_asString,
      Pos.Raw.extract.go₁_append_right _ _ _ _ _ (by rfl)]
    apply Pos.Raw.extract.go₂_append_left; apply Nat.add_comm

theorem splitAux_of_valid (p l m r acc) :
    splitAux (mk (l ++ m ++ r)) p ⟨utf8Len l⟩ ⟨utf8Len l + utf8Len m⟩ acc =
      acc.reverse ++ (List.splitOnP.go p r m.reverse).map mk := by
  unfold splitAux
  simp only [List.append_assoc, atEnd_iff, rawEndPos_mk, utf8Len_append, Pos.Raw.mk_le_mk,
    Nat.add_le_add_iff_left, (by omega : utf8Len m + utf8Len r ≤ utf8Len m ↔ utf8Len r = 0),
    utf8Len_eq_zero, List.reverse_cons, dite_eq_ite]
  split
  · subst r; simpa [List.splitOnP.go] using extract_of_valid l m []
  · obtain ⟨c, r, rfl⟩ := r.exists_cons_of_ne_nil ‹_›
    simp only [by
      simpa [-String.mk_eq_asString] using
        (⟨get_of_valid (l ++ m) (c :: r), next_of_valid (l ++ m) c r,
            extract_of_valid l m (c :: r)⟩ :
          _ ∧ _ ∧ _),
      List.splitOnP.go, List.reverse_reverse]
    split <;> rename_i h
    · simpa [-String.mk_eq_asString, Nat.add_assoc]
        using splitAux_of_valid p (l++m++[c]) [] r ((mk m)::acc)
    · simpa [-String.mk_eq_asString, Nat.add_assoc] using splitAux_of_valid p l (m++[c]) r acc

theorem splitToList_of_valid (s p) : splitToList s p = (List.splitOnP p s.data).map mk := by
  simpa [splitToList] using splitAux_of_valid p [] [] s.data []

@[deprecated splitToList_of_valid (since := "2025-10-18")]
theorem split_of_valid (s p) : splitToList s p = (List.splitOnP p s.data).map mk :=
  splitToList_of_valid s p

-- TODO: splitOn

@[simp] theorem toString_toSubstring (s : String) : s.toSubstring.toString = s :=
  extract_zero_rawEndPos _

attribute [simp] toSubstring'

theorem join_eq (ss : List String) : join ss = mk (ss.map data).flatten := by
  suffices ∀ (ss : List String) t, ss.foldl (· ++ ·) t = mk (t.data ++ (ss.map data).flatten) by
    simpa [join] using this ss ""
  intro ss t
  induction ss generalizing t with
  | nil => simp
  | cons s ss ih => simp [ih]

@[simp] theorem data_join (ss : List String) : (join ss).data = (ss.map data).flatten := by
  simp [join_eq]

namespace Iterator

@[simp] theorem forward_eq_nextn : forward = nextn := by
  funext it n; induction n generalizing it <;> simp [forward, nextn, *]

theorem hasNext_cons_addChar (c : Char) (cs : List Char) (i : Pos.Raw) :
    hasNext ⟨String.mk (c :: cs), i + c⟩ = hasNext ⟨String.mk cs, i⟩ := by
  simp [hasNext, Nat.add_lt_add_iff_right]

/-- Validity for a string iterator. -/
def Valid (it : Iterator) : Prop := it.pos.Valid it.s

/-- `it.ValidFor l r` means that `it` is a string iterator whose underlying string is
`l.reverse ++ r`, and where the cursor is pointing at the end of `l.reverse`. -/
inductive ValidFor (l r : List Char) : Iterator → Prop
  /-- The canonical constructor for `ValidFor`. -/
  | mk : ValidFor l r ⟨String.mk (l.reverseAux r), ⟨utf8Len l⟩⟩

attribute [simp] toString pos

namespace ValidFor

theorem valid : ∀ {it}, ValidFor l r it → Valid it
  | _, ⟨⟩ => by simpa [List.reverseAux_eq] using Pos.Raw.Valid.mk l.reverse r rfl

theorem out : ∀ {it}, ValidFor l r it → it = ⟨String.mk (l.reverseAux r), ⟨utf8Len l⟩⟩
  | _, ⟨⟩ => rfl

theorem out' :
    ∀ {it}, ValidFor l r it → it = ⟨String.mk (l.reverse ++ r), ⟨utf8Len l.reverse⟩⟩
  | _, ⟨⟩ => by simp [List.reverseAux_eq]

theorem mk' : ValidFor l r ⟨String.mk (l.reverse ++ r), ⟨utf8Len l.reverse⟩⟩ := by
  simpa [List.reverseAux_eq] using mk

theorem of_eq : ∀ it, it.1.data = l.reverseAux r → it.2.1 = utf8Len l → ValidFor l r it
  | ⟨s, ⟨_⟩⟩, h, rfl => by
    rw [← s.asString_data, ← String.mk_eq_asString, h]
    exact ⟨⟩

theorem _root_.String.validFor_mkIterator (s) : (mkIterator s).ValidFor [] s.data :=
  .of_eq _ (by simp [mkIterator]) (by simp [mkIterator])

theorem remainingBytes : ∀ {it}, ValidFor l r it → it.remainingBytes = utf8Len r
  | _, ⟨⟩ => by simp [-String.mk_eq_asString, Iterator.remainingBytes, Nat.add_sub_cancel_left,
    rawEndPos_mk]

theorem toString : ∀ {it}, ValidFor l r it → it.1 = String.mk (l.reverseAux r)
  | _, ⟨⟩ => rfl

theorem pos : ∀ {it}, ValidFor l r it → it.2 = ⟨utf8Len l⟩
  | _, ⟨⟩ => rfl

theorem pos_eq_zero {l r it} (h : ValidFor l r it) : it.2 = 0 ↔ l = [] := by
  simp [h.pos, Pos.Raw.ext_iff]

theorem pos_eq_rawEndPos {l r it} (h : ValidFor l r it) : it.2 = it.1.rawEndPos ↔ r = [] := by
  simp only [h.pos, h.toString, rawEndPos_mk, utf8Len_reverseAux, Pos.Raw.ext_iff]
  exact (Nat.add_left_cancel_iff (m := 0)).trans <| eq_comm.trans utf8Len_eq_zero

@[deprecated pos_eq_rawEndPos (since := "2025-10-21")]
theorem pos_eq_endPos {l r it} (h : ValidFor l r it) : it.2 = it.1.rawEndPos ↔ r = [] :=
  pos_eq_rawEndPos h

theorem curr : ∀ {it}, ValidFor l r it → it.curr = r.headD default
  | it, h => by cases h.out'; apply get_of_valid

theorem next : ∀ {it}, ValidFor l (c :: r) it → ValidFor (c :: l) r it.next
  | it, h => by
    cases h.out'
    simp only [Iterator.next, next_of_valid l.reverse c r]
    rw [← List.reverseAux_eq, utf8Len_reverse]; constructor

theorem prev : ∀ {it}, ValidFor (c :: l) r it → ValidFor l (c :: r) it.prev
  | it, h => by
    cases h.out'
    have := prev_of_valid l.reverse c r
    simp only [utf8Len_reverse] at this
    simp only [Iterator.prev, List.reverse_cons, List.append_assoc, List.singleton_append,
      utf8Len_append, utf8Len_reverse, utf8Len_cons, utf8Len_nil, Nat.zero_add, this]
    exact .of_eq _ (by simp [List.reverseAux_eq]) (by simp)

theorem prev_nil : ∀ {it}, ValidFor [] r it → ValidFor [] r it.prev
  | it, h => by
    simp only [Iterator.prev, h.toString, List.reverseAux_nil, h.pos, utf8Len_nil,
      Pos.Raw.mk_zero, Pos.Raw.prev_zero]
    constructor

theorem atEnd : ∀ {it}, ValidFor l r it → (it.atEnd ↔ r = [])
  | it, h => by
    simp only [Iterator.atEnd, h.pos, h.toString, rawEndPos_mk, utf8Len_reverseAux, ge_iff_le,
      decide_eq_true_eq]
    exact Nat.add_le_add_iff_left.trans <| Nat.le_zero.trans utf8Len_eq_zero

theorem hasNext : ∀ {it}, ValidFor l r it → (it.hasNext ↔ r ≠ [])
  | it, h => by simp [Iterator.hasNext, ← h.atEnd, Iterator.atEnd]

theorem hasPrev : ∀ {it}, ValidFor l r it → (it.hasPrev ↔ l ≠ [])
  | it, h => by simp [Iterator.hasPrev, h.pos, Nat.pos_iff_ne_zero]

theorem setCurr' : ∀ {it}, ValidFor l r it →
    ValidFor l (r.modifyHead fun _ => c) (it.setCurr c)
  | it, h => by
    cases h.out'
    simp only [setCurr, utf8Len_reverse]
    refine .of_eq _ ?_ (by simp)
    have := set_of_valid l.reverse r c
    simp only [utf8Len_reverse] at this; simp [-String.mk_eq_asString, List.reverseAux_eq, this]

theorem setCurr (h : ValidFor l (c :: r) it) :
    ValidFor l (c :: r) (it.setCurr c) := h.setCurr'

theorem toEnd (h : ValidFor l r it) : ValidFor (r.reverse ++ l) [] it.toEnd := by
  simp only [Iterator.toEnd, h.toString, rawEndPos_mk, utf8Len_reverseAux]
  exact .of_eq _ (by simp [List.reverseAux_eq]) (by simp [Nat.add_comm])

theorem toEnd' (it : Iterator) : ValidFor it.s.data.reverse [] it.toEnd := by
  simp only [Iterator.toEnd]
  exact .of_eq _ (by simp [List.reverseAux_eq])
    (by simp [-size_bytes, -String.mk_eq_asString, rawEndPos, utf8ByteSize])

theorem extract (h₁ : ValidFor l (m ++ r) it₁)
    (h₂ : ValidFor (m.reverse ++ l) r it₂) : it₁.extract it₂ = String.mk m := by
  cases h₁.out; cases h₂.out
  simp only [Iterator.extract, List.reverseAux_eq, List.reverse_append, List.reverse_reverse,
    List.append_assoc, ne_eq, not_true_eq_false, decide_false, utf8Len_append, utf8Len_reverse,
    gt_iff_lt, Pos.Raw.lt_iff, Nat.not_lt.2 (Nat.le_add_left ..), Bool.or_self, Bool.false_eq_true,
    ↓reduceIte]
  simpa [Nat.add_comm] using extract_of_valid l.reverse m r

theorem remainingToString {it} (h : ValidFor l r it) :
    it.remainingToString = String.mk r := by
  cases h.out
  simpa [-String.mk_eq_asString, rawEndPos_mk, Iterator.remainingToString, List.reverseAux_eq]
    using extract_of_valid l.reverse r []

theorem nextn : ∀ {it}, ValidFor l r it →
      ∀ n, n ≤ r.length → ValidFor ((r.take n).reverse ++ l) (r.drop n) (it.nextn n)
  | it, h, 0, _ => by simp [h, Iterator.nextn]
  | it, h, n+1, hn => by
    simp only [Iterator.nextn]
    have a::r := r
    simpa using h.next.nextn _ (Nat.le_of_succ_le_succ hn)

theorem prevn : ∀ {it}, ValidFor l r it →
      ∀ n, n ≤ l.length → ValidFor (l.drop n) ((l.take n).reverse ++ r) (it.prevn n)
  | it, h, 0, _ => by simp [h, Iterator.prevn]
  | it, h, n+1, hn => by
    simp only [Iterator.prevn]
    have a::l := l
    simpa using h.prev.prevn _ (Nat.le_of_succ_le_succ hn)

end ValidFor

namespace Valid

theorem validFor : ∀ {it}, Valid it → ∃ l r, ValidFor l r it
  | ⟨_, ⟨_⟩⟩, .mk l r rfl =>
    ⟨l.reverse, r, by simpa [List.reverseAux_eq] using @ValidFor.mk l.reverse r⟩

theorem _root_.String.valid_mkIterator (s) : (mkIterator s).Valid := s.validFor_mkIterator.valid

theorem remainingBytes_le : ∀ {it}, Valid it → it.remainingBytes ≤ utf8ByteSize it.s
  | _, h =>
    let ⟨l, r, h⟩ := h.validFor
    by simp [-String.mk_eq_asString, utf8ByteSize_mk, h.remainingBytes, h.toString, Nat.le_add_left]

theorem next : ∀ {it}, Valid it → it.hasNext → Valid it.next
  | _, h, hn => by
    let ⟨l, r, h⟩ := h.validFor
    obtain ⟨c, r, rfl⟩ := List.exists_cons_of_ne_nil (h.hasNext.1 hn)
    exact h.next.valid

theorem prev : ∀ {it}, Valid it → Valid it.prev
  | _, h =>
    match h.validFor with
    | ⟨[], _, h⟩ => h.prev_nil.valid
    | ⟨_::_, _, h⟩ => h.prev.valid

theorem setCurr : ∀ {it}, Valid it → Valid (it.setCurr c)
  | it, h => by
    let ⟨l, r, h⟩ := h.validFor
    exact h.setCurr'.valid

theorem toEnd (it : String.Iterator) : Valid it.toEnd := (ValidFor.toEnd' _).valid

theorem remainingToString {it} (h : ValidFor l r it) :
    it.remainingToString = String.mk r := by
  cases h.out
  simpa [-String.mk_eq_asString, rawEndPos_mk, Iterator.remainingToString, List.reverseAux_eq]
    using extract_of_valid l.reverse r []

theorem prevn (h : Valid it) : ∀ n, Valid (it.prevn n)
  | 0 => h
  | n+1 => h.prev.prevn n

end Valid
end Iterator

@[nolint unusedHavesSuffices] -- false positive from unfolding String.offsetOfPosAux
theorem offsetOfPosAux_of_valid : ∀ l m r n,
    offsetOfPosAux (mk (l ++ m ++ r)) ⟨utf8Len l + utf8Len m⟩ ⟨utf8Len l⟩ n = n + m.length
  | l, [], r, n => by unfold offsetOfPosAux; simp
  | l, c::m, r, n => by
    unfold offsetOfPosAux
    rw [if_neg (by exact Nat.not_le.2 (Nat.lt_add_of_pos_right add_utf8Size_pos))]
    simp only [List.append_assoc, atEnd_of_valid l (c::m++r)]
    simp only [List.cons_append, utf8Len_cons, next_of_valid l c (m ++ r)]
    simpa [← Nat.add_assoc, Nat.add_right_comm] using
      offsetOfPosAux_of_valid (l++[c]) m r (n + 1)

theorem offsetOfPos_of_valid (l r) : offsetOfPos (mk (l ++ r)) ⟨utf8Len l⟩ = l.length := by
  simpa using offsetOfPosAux_of_valid [] l r 0

@[nolint unusedHavesSuffices] -- false positive from unfolding String.foldlAux
theorem foldlAux_of_valid (f : α → Char → α) : ∀ l m r a,
    foldlAux f (mk (l ++ m ++ r)) ⟨utf8Len l + utf8Len m⟩ ⟨utf8Len l⟩ a = m.foldl f a
  | l, [], r, a => by unfold foldlAux; simp
  | l, c::m, r, a => by
    unfold foldlAux
    rw [dif_pos (by exact Nat.lt_add_of_pos_right add_utf8Size_pos)]
    simp only [List.append_assoc, List.cons_append, utf8Len_cons, next_of_valid l c (m ++ r),
      get_of_valid l (c :: (m ++ r)), Char.reduceDefault, List.headD_cons, List.foldl_cons]
    simpa [← Nat.add_assoc, Nat.add_right_comm] using foldlAux_of_valid f (l++[c]) m r (f a c)

theorem foldl_eq (f : α → Char → α) (s a) : foldl f a s = s.data.foldl f a := by
  simpa using foldlAux_of_valid f [] s.data [] a

@[nolint unusedHavesSuffices] -- false positive from unfolding String.foldrAux
theorem foldrAux_of_valid (f : Char → α → α) (l m r a) :
    foldrAux f a (mk (l ++ m ++ r)) ⟨utf8Len l + utf8Len m⟩ ⟨utf8Len l⟩ = m.foldr f a := by
  rw [← m.reverse_reverse]
  induction m.reverse generalizing r a with (unfold foldrAux; simp)
  | cons c m IH =>
    rw [if_pos add_utf8Size_pos]
    simp only [← Nat.add_assoc, by simpa using prev_of_valid (l ++ m.reverse) c r]
    simp only [by simpa using get_of_valid (l ++ m.reverse) (c :: r)]
    simpa using IH (c::r) (f c a)

theorem foldr_eq (f : Char → α → α) (s a) : foldr f a s = s.data.foldr f a := by
  simpa using foldrAux_of_valid f [] s.data [] a

@[nolint unusedHavesSuffices] -- false positive from unfolding String.anyAux
theorem anyAux_of_valid (p : Char → Bool) : ∀ l m r,
    anyAux (mk (l ++ m ++ r)) ⟨utf8Len l + utf8Len m⟩ p ⟨utf8Len l⟩ = m.any p
  | l, [], r => by unfold anyAux; simp
  | l, c::m, r => by
    unfold anyAux
    rw [dif_pos (by exact Nat.lt_add_of_pos_right add_utf8Size_pos)]
    simp only [List.append_assoc, List.cons_append, get_of_valid l (c :: (m ++ r)),
      Char.reduceDefault, List.headD_cons, utf8Len_cons, next_of_valid l c (m ++ r),
      Bool.if_true_left, Bool.decide_eq_true, List.any_cons]
    cases p c <;> simp
    simpa [← Nat.add_assoc, Nat.add_right_comm] using anyAux_of_valid p (l++[c]) m r

theorem any_eq (s : String) (p : Char → Bool) : any s p = s.data.any p := by
  simpa using anyAux_of_valid p [] s.data []

theorem any_iff (s : String) (p : Char → Bool) : any s p ↔ ∃ c ∈ s.data, p c := by simp [any_eq]

theorem all_eq (s : String) (p : Char → Bool) : all s p = s.data.all p := by
  rw [all, any_eq, List.all_eq_not_any_not]

theorem all_iff (s : String) (p : Char → Bool) : all s p ↔ ∀ c ∈ s.data, p c := by simp [all_eq]

theorem contains_iff (s : String) (c : Char) : contains s c ↔ c ∈ s.data := by
  simp [contains, any_iff]

@[nolint unusedHavesSuffices] -- false positive from unfolding String.mapAux
theorem mapAux_of_valid (f : Char → Char) :
    ∀ l r, mapAux f ⟨utf8Len l⟩ (mk (l ++ r)) = mk (l ++ r.map f)
  | l, [] => by unfold mapAux; simp
  | l, c::r => by
    unfold mapAux
    rw [dif_neg (by rw [atEnd_of_valid]; simp)]
    simp only [← String.mk_eq_asString, get_of_valid l (c :: r), Char.reduceDefault,
      List.headD_cons, set_of_valid l (c :: r), List.modifyHead_cons, next_of_valid l (f c) r,
      List.map_cons]
    simpa using mapAux_of_valid f (l++[f c]) r

theorem map_eq (f : Char → Char) (s) : map f s = mk (s.data.map f) := by
  simpa using mapAux_of_valid f [] s.data

-- TODO: substrEq
-- TODO: isPrefixOf
-- TODO: replace

@[nolint unusedHavesSuffices] -- false positive from unfolding String.takeWhileAux
theorem takeWhileAux_of_valid (p : Char → Bool) : ∀ l m r,
    Substring.takeWhileAux (mk (l ++ m ++ r)) ⟨utf8Len l + utf8Len m⟩ p ⟨utf8Len l⟩ =
      ⟨utf8Len l + utf8Len (m.takeWhile p)⟩
  | l, [], r => by unfold Substring.takeWhileAux List.takeWhile; simp
  | l, c::m, r => by
    unfold Substring.takeWhileAux List.takeWhile
    rw [dif_pos (by exact Nat.lt_add_of_pos_right add_utf8Size_pos)]
    simp only [List.append_assoc, List.cons_append, get_of_valid l (c :: (m ++ r)),
      Char.reduceDefault, List.headD_cons, utf8Len_cons, next_of_valid l c (m ++ r)]
    cases p c <;> simp
    simpa [← Nat.add_assoc, Nat.add_right_comm] using takeWhileAux_of_valid p (l++[c]) m r

@[simp]
theorem map_eq_empty_iff (s : String) (f : Char → Char) : (s.map f) = "" ↔ s = "" := by
  simp only [map_eq, ← data_eq_nil_iff, String.mk_eq_asString, List.data_asString,
    List.map_eq_nil_iff]

@[simp]
theorem map_isEmpty_eq_isEmpty (s : String) (f : Char → Char) : (s.map f).isEmpty = s.isEmpty := by
  rw [Bool.eq_iff_iff]; simp [isEmpty_iff, map_eq_empty_iff]

@[simp]
theorem length_map (s : String) (f : Char → Char) : (s.map f).length = s.length := by
  simp only [← length_data, map_eq, String.mk_eq_asString, List.data_asString, List.length_map]

theorem length_eq_of_map_eq {a b : String} {f g : Char → Char} :
  a.map f = b.map g → a.length = b.length := by
  intro h; rw [← length_map a f, ← length_map b g, h]

end String

open String

namespace Substring

/-- Validity for a substring. -/
structure Valid (s : Substring) : Prop where
  /-- The start position of a valid substring is valid. -/
  startValid : s.startPos.Valid s.str
  /-- The stop position of a valid substring is valid. -/
  stopValid : s.stopPos.Valid s.str
  /-- The stop position of a substring is at least the start. -/
  le : s.startPos ≤ s.stopPos

theorem Valid_default : Valid default := ⟨Pos.Raw.valid_zero, Pos.Raw.valid_zero, Nat.le_refl _⟩

/-- A substring is represented by three lists `l m r`, where `m` is the middle section
(the actual substring) and `l ++ m ++ r` is the underlying string. -/
inductive ValidFor (l m r : List Char) : Substring → Prop
  /-- The constructor for `ValidFor`. -/
  | mk : ValidFor l m r ⟨String.mk (l ++ m ++ r), ⟨utf8Len l⟩, ⟨utf8Len l + utf8Len m⟩⟩

namespace ValidFor

theorem valid : ∀ {s}, ValidFor l m r s → Valid s
  | _, ⟨⟩ => ⟨.intro ⟨l, m ++ r, by simp⟩, .intro ⟨l ++ m, r, by simp⟩, Nat.le_add_right ..⟩

theorem of_eq : ∀ s,
    s.str.data = l ++ m ++ r →
    s.startPos.1 = utf8Len l →
    s.stopPos.1 = utf8Len l + utf8Len m →
    ValidFor l m r s
  | ⟨s, ⟨_⟩, ⟨_⟩⟩, h, rfl, rfl => by
    rw [← s.asString_data, h]
    exact ⟨⟩

theorem _root_.String.validFor_toSubstring (s : String) : ValidFor [] s.data [] s :=
  .of_eq _ (by simp [toSubstring]) rfl (by simp [toSubstring, rawEndPos])

theorem str : ∀ {s}, ValidFor l m r s → s.str = String.mk (l ++ m ++ r)
  | _, ⟨⟩ => rfl

theorem startPos : ∀ {s}, ValidFor l m r s → s.startPos = ⟨utf8Len l⟩
  | _, ⟨⟩ => rfl

theorem stopPos : ∀ {s}, ValidFor l m r s → s.stopPos = ⟨utf8Len l + utf8Len m⟩
  | _, ⟨⟩ => rfl

theorem bsize : ∀ {s}, ValidFor l m r s → s.bsize = utf8Len m
  | _, ⟨⟩ => by simp [Substring.bsize, Nat.add_sub_cancel_left]

theorem isEmpty : ∀ {s}, ValidFor l m r s → (s.isEmpty ↔ m = [])
  | _, h => by simp [Substring.isEmpty, h.bsize]

theorem toString : ∀ {s}, ValidFor l m r s → s.toString = String.mk m
  | _, ⟨⟩ => extract_of_valid l m r

theorem toIterator : ∀ {s}, ValidFor l m r s → s.toIterator.ValidFor l.reverse (m ++ r)
  | _, h => by
    simp only [Substring.toIterator]
    exact .of_eq _ (by simp [h.str, List.reverseAux_eq]) (by simp [h.startPos])

theorem get : ∀ {s}, ValidFor l (m₁ ++ c :: m₂) r s → s.get ⟨utf8Len m₁⟩ = c
  | _, ⟨⟩ => by simpa using get_of_valid (l ++ m₁) (c :: m₂ ++ r)

theorem next : ∀ {s}, ValidFor l (m₁ ++ c :: m₂) r s →
    s.next ⟨utf8Len m₁⟩ = ⟨utf8Len m₁ + c.utf8Size⟩
  | _, ⟨⟩ => by
    simp only [Substring.next, utf8Len_append, utf8Len_cons, List.append_assoc, List.cons_append]
    rw [if_neg (mt Pos.Raw.ext_iff.1 ?a)]
    case a =>
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        @ne_add_utf8Size_add_self (utf8Len l + utf8Len m₁) (utf8Len m₂) c
    have := next_of_valid (l ++ m₁) c (m₂ ++ r)
    simp only [List.append_assoc, utf8Len_append, Pos.Raw.offsetBy_eq] at this ⊢; rw [this]
    simp [Nat.add_assoc, Nat.add_sub_cancel_left]

theorem next_stop : ∀ {s}, ValidFor l m r s → s.next ⟨utf8Len m⟩ = ⟨utf8Len m⟩
  | _, ⟨⟩ => by simp [Substring.next, Pos.Raw.offsetBy_eq]

theorem prev : ∀ {s}, ValidFor l (m₁ ++ c :: m₂) r s →
    s.prev ⟨utf8Len m₁ + c.utf8Size⟩ = ⟨utf8Len m₁⟩
  | _, ⟨⟩ => by
    simp only [Substring.prev, List.append_assoc, List.cons_append]
    rw [if_neg (mt Pos.Raw.ext_iff.1 <| Ne.symm ?a)]
    case a => simpa [Nat.add_comm] using @ne_add_utf8Size_add_self (utf8Len l) (utf8Len m₁) c
    have := prev_of_valid (l ++ m₁) c (m₂ ++ r)
    simp only [List.append_assoc, utf8Len_append, Nat.add_assoc,
      Pos.Raw.offsetBy_eq] at this ⊢; rw [this]
    simp [Nat.add_sub_cancel_left]

theorem nextn_stop : ∀ {s}, ValidFor l m r s → ∀ n, s.nextn n ⟨utf8Len m⟩ = ⟨utf8Len m⟩
  | _, _, 0 => rfl
  | _, h, n+1 => by simp [Substring.nextn, h.next_stop, h.nextn_stop n]

theorem nextn : ∀ {s}, ValidFor l (m₁ ++ m₂) r s →
    ∀ n, s.nextn n ⟨utf8Len m₁⟩ = ⟨utf8Len m₁ + utf8Len (m₂.take n)⟩
  | _, _, 0 => by simp [Substring.nextn]
  | s, h, n+1 => by
    simp only [Substring.nextn]
    match m₂ with
    | [] => simp at h; simp [h.next_stop, h.nextn_stop]
    | c::m₂ =>
      rw [h.next]
      have := @nextn l (m₁ ++ [c]) m₂ r s (by simp [h]) n
      simp at this; rw [this]; simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem prevn : ∀ {s}, ValidFor l (m₁.reverse ++ m₂) r s →
    ∀ n, s.prevn n ⟨utf8Len m₁⟩ = ⟨utf8Len (m₁.drop n)⟩
  | _, _, 0 => by simp [Substring.prevn]
  | s, h, n+1 => by
    simp only [Substring.prevn]
    match m₁ with
    | [] => simp
    | c::m₁ =>
      rw [List.reverse_cons, List.append_assoc] at h
      have := h.prev; simp at this; simp [this, h.prevn n]

theorem front : ∀ {s}, ValidFor l (c :: m) r s → s.front = c
  | _, h => h.get (m₁ := [])

theorem drop :
    ∀ {s}, ValidFor l m r s → ∀ n, ValidFor (l ++ m.take n) (m.drop n) r (s.drop n)
  | s, h, n => by
    have : Substring.nextn {..} .. = _ := h.nextn (m₁ := []) n
    simp only [utf8Len_nil, Pos.Raw.mk_zero, Nat.zero_add] at this
    simp only [Substring.drop, this]
    simp only [h.str, List.append_assoc, h.startPos, h.stopPos]
    rw [← List.take_append_drop n m] at h
    refine .of_eq _ (by simp) (by simp) ?_
    conv => lhs; rw [← List.take_append_drop n m]
    simp [-List.take_append_drop, Nat.add_assoc]

theorem take : ∀ {s}, ValidFor l m r s → ∀ n, ValidFor l (m.take n) (m.drop n ++ r) (s.take n)
  | s, h, n => by
    have : Substring.nextn {..} .. = _ := h.nextn (m₁ := []) n
    simp at this
    simp only [Substring.take, this]
    simp only [h.str, List.append_assoc, h.startPos]
    rw [← List.take_append_drop n m] at h
    refine .of_eq _ ?_ (by simp) (by simp)
    conv => lhs; rw [← List.take_append_drop n m]
    simp [-List.take_append_drop]

-- TODO: takeRight, dropRight

theorem atEnd : ∀ {s}, ValidFor l m r s → (s.atEnd ⟨p⟩ ↔ p = utf8Len m)
  | _, ⟨⟩ => by simp [Substring.atEnd, Pos.Raw.ext_iff, Nat.add_left_cancel_iff]

theorem extract' : ∀ {s}, ValidFor l (ml ++ mm ++ mr) r s →
    ValidFor ml mm mr ⟨String.mk (ml ++ mm ++ mr), b, e⟩ →
    ∃ l' r', ValidFor l' mm r' (s.extract b e)
  | _, ⟨⟩, ⟨⟩ => by
    simp only [Substring.extract, ge_iff_le, Pos.Raw.mk_le_mk, List.append_assoc, utf8Len_append]
    split
    · next h =>
      rw [utf8Len_eq_zero.1 <| Nat.le_zero.1 <| Nat.add_le_add_iff_left.1 h]
      exact ⟨[], [], ⟨⟩⟩
    · next h =>
      refine ⟨l ++ ml, mr ++ r, .of_eq _ (by simp) ?_ ?_⟩ <;>
        simp only [Pos.Raw.byteIdx_offsetBy, Nat.min_eq_min, utf8Len_append]
          <;> rw [Nat.min_eq_right]
          <;> try simp [Nat.add_le_add_iff_left, Nat.le_add_right]
      rw [Nat.add_assoc]

theorem extract : ∀ {s}, ValidFor l m r s →
    ValidFor ml mm mr ⟨String.mk m, b, e⟩ → ∃ l' r', ValidFor l' mm r' (s.extract b e) := by
  intro s h₁ h₂
  obtain rfl : m = ml ++ mm ++ mr := by simpa using congrArg String.data h₂.str
  exact extract' h₁ h₂

-- TODO: splitOn

theorem foldl (f) (init : α) : ∀ {s}, ValidFor l m r s → s.foldl f init = m.foldl f init
  | _, ⟨⟩ => by simp [-String.mk_eq_asString, -List.append_assoc, Substring.foldl,
    foldlAux_of_valid]

theorem foldr (f) (init : α) : ∀ {s}, ValidFor l m r s → s.foldr f init = m.foldr f init
  | _, ⟨⟩ => by simp [-String.mk_eq_asString, -List.append_assoc, Substring.foldr,
    foldrAux_of_valid]

theorem any (f) : ∀ {s}, ValidFor l m r s → s.any f = m.any f
  | _, ⟨⟩ => by simp [-String.mk_eq_asString, -List.append_assoc, Substring.any, anyAux_of_valid]

theorem all (f) : ∀ {s}, ValidFor l m r s → s.all f = m.all f
  | _, h => by simp [Substring.all, h.any, List.all_eq_not_any_not]

theorem contains (c) : ∀ {s}, ValidFor l m r s → (s.contains c ↔ c ∈ m)
  | _, h => by simp [Substring.contains, h.any]

theorem takeWhile (p : Char → Bool) : ∀ {s}, ValidFor l m r s →
    ValidFor l (m.takeWhile p) (m.dropWhile p ++ r) (s.takeWhile p)
  | _, ⟨⟩ => by
    simp only [Substring.takeWhile, takeWhileAux_of_valid]
    apply ValidFor.of_eq <;> simp
    rw [← List.append_assoc, List.takeWhile_append_dropWhile]

theorem dropWhile (p : Char → Bool) : ∀ {s}, ValidFor l m r s →
    ValidFor (l ++ m.takeWhile p) (m.dropWhile p) r (s.dropWhile p)
  | _, ⟨⟩ => by
    simp only [Substring.dropWhile, takeWhileAux_of_valid]
    apply ValidFor.of_eq <;> simp
    rw [Nat.add_assoc, ← utf8Len_append (m.takeWhile p), List.takeWhile_append_dropWhile]

-- TODO: takeRightWhile

end ValidFor

namespace Valid

theorem validFor : ∀ {s}, Valid s → ∃ l m r, ValidFor l m r s
  | ⟨_, ⟨_⟩, ⟨_⟩⟩, ⟨.mk l mr rfl, t, h⟩ => by
    obtain ⟨lm, r, h₁, h₂⟩ := t.exists
    have e : lm ++ r = l ++ mr := by
      simpa [← List.asString_inj, ← String.bytes_inj] using h₁
    obtain rfl := Pos.Raw.ext_iff.1 h₂
    simp only [Pos.Raw.mk_le_mk] at *
    have := (or_iff_right_iff_imp.2 fun h => ?x).1 (List.append_eq_append_iff.1 e)
    case x =>
      match l, r, h with | _, _, ⟨m, rfl, rfl⟩ => ?_
      simp only [utf8Len_append] at h
      cases utf8Len_eq_zero.1 <| Nat.le_zero.1 (Nat.le_of_add_le_add_left (c := 0) h)
      exact ⟨[], by simp⟩
    match lm, mr, this with
    | _, _, ⟨m, rfl, rfl⟩ => exact ⟨l, m, r, by simpa using ValidFor.mk⟩

theorem valid : ∀ {s}, ValidFor l m r s → Valid s
  | _, ⟨⟩ => ⟨.intro ⟨l, m ++ r, by simp, by simp⟩,
    .intro ⟨l ++ m, r, by simp, by simp⟩, Nat.le_add_right ..⟩

theorem _root_.String.valid_toSubstring (s : String) : Valid s :=
  s.validFor_toSubstring.valid

theorem bsize : ∀ {s}, Valid s → s.bsize = utf8Len s.toString.data
  | _, h => let ⟨l, m, r, h⟩ := h.validFor; by simp [h.bsize, h.toString]

theorem isEmpty : ∀ {s}, Valid s → (s.isEmpty ↔ s.toString = "")
  | _, h => let ⟨l, m, r, h⟩ := h.validFor; by simp [h.isEmpty, h.toString, String.ext_iff]

theorem get : ∀ {s}, Valid s → s.toString.data = m₁ ++ c :: m₂ → s.get ⟨utf8Len m₁⟩ = c
  | _, h, e => by
    let ⟨l, m, r, h⟩ := h.validFor
    simp only [h.toString, String.mk_eq_asString, List.data_asString] at e; subst e; simp [h.get]

theorem next : ∀ {s}, Valid s → s.toString.data = m₁ ++ c :: m₂ →
    s.next ⟨utf8Len m₁⟩ = ⟨utf8Len m₁ + c.utf8Size⟩
  | _, h, e => by
    let ⟨l, m, r, h⟩ := h.validFor
    simp only [h.toString, String.mk_eq_asString, List.data_asString] at e; subst e; simp [h.next]

theorem next_stop : ∀ {s}, Valid s → s.next ⟨s.bsize⟩ = ⟨s.bsize⟩
  | _, h => let ⟨l, m, r, h⟩ := h.validFor; by simp [h.bsize, h.next_stop]

theorem prev : ∀ {s}, Valid s → s.toString.data = m₁ ++ c :: m₂ →
    s.prev ⟨utf8Len m₁ + c.utf8Size⟩ = ⟨utf8Len m₁⟩
  | _, h, e => by
    let ⟨l, m, r, h⟩ := h.validFor
    simp only [h.toString, String.mk_eq_asString, List.data_asString] at e; subst e; simp [h.prev]

theorem nextn_stop : ∀ {s}, Valid s → ∀ n, s.nextn n ⟨s.bsize⟩ = ⟨s.bsize⟩
  | _, h, n => let ⟨l, m, r, h⟩ := h.validFor; by simp [h.bsize, h.nextn_stop]

theorem nextn : ∀ {s}, Valid s → s.toString.data = m₁ ++ m₂ →
    ∀ n, s.nextn n ⟨utf8Len m₁⟩ = ⟨utf8Len m₁ + utf8Len (m₂.take n)⟩
  | _, h, e => by
    let ⟨l, m, r, h⟩ := h.validFor
    simp only [h.toString, String.mk_eq_asString, List.data_asString] at e; subst e; simp [h.nextn]

theorem prevn : ∀ {s}, Valid s → s.toString.data = m₁.reverse ++ m₂ →
    ∀ n, s.prevn n ⟨utf8Len m₁⟩ = ⟨utf8Len (m₁.drop n)⟩
  | _, h, e => by
    let ⟨l, m, r, h⟩ := h.validFor
    simp only [h.toString, String.mk_eq_asString, List.data_asString] at e; subst e; simp [h.prevn]

theorem front : ∀ {s}, Valid s → s.toString.data = c :: m → s.front = c
  | _, h => h.get (m₁ := [])

theorem drop : ∀ {s}, Valid s → ∀ n, Valid (s.drop n)
  | _, h, _ => let ⟨_, _, _, h⟩ := h.validFor; (h.drop _).valid

theorem data_drop : ∀ {s}, Valid s → ∀ n, (s.drop n).toString.data = s.toString.data.drop n
  | _, h, _ => let ⟨_, _, _, h⟩ := h.validFor; by simp [(h.drop _).toString, h.toString]

theorem take : ∀ {s}, Valid s → ∀ n, Valid (s.take n)
  | _, h, _ => let ⟨_, _, _, h⟩ := h.validFor; (h.take _).valid

theorem data_take : ∀ {s}, Valid s → ∀ n, (s.take n).toString.data = s.toString.data.take n
  | _, h, _ => let ⟨_, _, _, h⟩ := h.validFor; by simp [(h.take _).toString, h.toString]

-- TODO: takeRight, dropRight

theorem atEnd : ∀ {s}, Valid s → (s.atEnd ⟨p⟩ ↔ p = utf8ByteSize s.toString)
  | _, h => let ⟨_, _, _, h⟩ := h.validFor; by simp [-String.mk_eq_asString, utf8ByteSize_mk,
    h.atEnd, h.toString]

theorem extract : ∀ {s}, Valid s → Valid ⟨s.toString, b, e⟩ → Valid (s.extract b e)
  | _, h₁, h₂ => by
    let ⟨l, m, r, h₁⟩ := h₁.validFor
    rw [h₁.toString] at h₂
    let ⟨ml, mm, mr, h₂⟩ := h₂.validFor
    have ⟨l', r', h₃⟩ := h₁.extract h₂
    exact h₃.valid

theorem toString_extract : ∀ {s}, Valid s → Valid ⟨s.toString, b, e⟩ →
    (s.extract b e).toString = String.Pos.Raw.extract s.toString b e
  | _, h₁, h₂ => by
    let ⟨l, m, r, h₁⟩ := h₁.validFor
    rw [h₁.toString] at h₂
    let ⟨ml, mm, mr, h₂⟩ := h₂.validFor
    have ⟨l', r', h₃⟩ := h₁.extract h₂
    rw [h₃.toString, h₁.toString, ← h₂.toString, toString]

theorem foldl (f) (init : α) : ∀ {s}, Valid s → s.foldl f init = s.toString.data.foldl f init
  | _, h => let ⟨_, _, _, h⟩ := h.validFor; by simp [h.foldl, h.toString]

theorem foldr (f) (init : α) : ∀ {s}, Valid s → s.foldr f init = s.toString.data.foldr f init
  | _, h => let ⟨_, _, _, h⟩ := h.validFor; by simp [h.foldr, h.toString]

theorem any (f) : ∀ {s}, Valid s → s.any f = s.toString.data.any f
  | _, h => let ⟨_, _, _, h⟩ := h.validFor; by simp [h.any, h.toString]

theorem all (f) : ∀ {s}, Valid s → s.all f = s.toString.data.all f
  | _, h => let ⟨_, _, _, h⟩ := h.validFor; by simp [h.all, h.toString]

theorem contains (c) : ∀ {s}, Valid s → (s.contains c ↔ c ∈ s.toString.data)
  | _, h => let ⟨_, _, _, h⟩ := h.validFor; by simp [h.contains, h.toString]

theorem takeWhile (p : Char → Bool) : ∀ {s}, Valid s → Valid (s.takeWhile p)
  | _, h => let ⟨_, _, _, h⟩ := h.validFor; (h.takeWhile _).valid

theorem data_takeWhile (p) : ∀ {s}, Valid s →
    (s.takeWhile p).toString.data = s.toString.data.takeWhile p
  | _, h => let ⟨_, _, _, h⟩ := h.validFor; by simp [(h.takeWhile _).toString, h.toString]

theorem dropWhile (p : Char → Bool) : ∀ {s}, Valid s → Valid (s.dropWhile p)
  | _, h => let ⟨_, _, _, h⟩ := h.validFor; (h.dropWhile _).valid

theorem data_dropWhile (p) : ∀ {s}, Valid s →
    (s.dropWhile p).toString.data = s.toString.data.dropWhile p
  | _, h => let ⟨_, _, _, h⟩ := h.validFor; by simp [(h.dropWhile _).toString, h.toString]

-- TODO: takeRightWhile

end Valid
end Substring

namespace String

theorem drop_eq (s : String) (n : Nat) : s.drop n = mk (s.data.drop n) :=
  (s.validFor_toSubstring.drop n).toString

@[simp] theorem data_drop (s : String) (n : Nat) : (s.drop n).data = s.data.drop n := by
  simp [drop_eq]

@[simp] theorem drop_empty {n : Nat} : "".drop n = "" := by simp [drop_eq, List.drop_nil]

theorem take_eq (s : String) (n : Nat) : s.take n = mk (s.data.take n) :=
  (s.validFor_toSubstring.take n).toString

@[simp] theorem data_take (s : String) (n : Nat) : (s.take n).data = s.data.take n := by
  simp [take_eq]

theorem takeWhile_eq (p : Char → Bool) (s : String) : s.takeWhile p = mk (s.data.takeWhile p) :=
  (s.validFor_toSubstring.takeWhile p).toString

@[simp] theorem data_takeWhile (p : Char → Bool) (s : String) :
    (s.takeWhile p).data = s.data.takeWhile p := by simp [takeWhile_eq]

theorem dropWhile_eq (p : Char → Bool) (s : String) : s.dropWhile p = mk (s.data.dropWhile p) :=
  (s.validFor_toSubstring.dropWhile p).toString

@[simp] theorem data_dropWhile (p : Char → Bool) (s : String) :
    (s.dropWhile p).data = s.data.dropWhile p := by simp [dropWhile_eq]

end String

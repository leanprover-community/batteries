/-
Copyright (c) 2023 Bulhwi Cha. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bulhwi Cha, Mario Carneiro
-/
import Batteries.Data.Char
import Batteries.Data.List.Lemmas
import Batteries.Data.String.Basic
import Batteries.Tactic.Lint.Misc
import Batteries.Tactic.SeqFocus

namespace String

-- TODO(kmill): add `@[ext]` attribute to `String.ext` in core.
attribute [ext (iff := false)] ext

theorem lt_trans {s₁ s₂ s₃ : String} : s₁ < s₂ → s₂ < s₃ → s₁ < s₃ :=
  List.lt_trans' (α := Char) Nat.lt_trans
    (fun h1 h2 => Nat.not_lt.2 <| Nat.le_trans (Nat.not_lt.1 h2) (Nat.not_lt.1 h1))

theorem lt_antisymm {s₁ s₂ : String} (h₁ : ¬s₁ < s₂) (h₂ : ¬s₂ < s₁) : s₁ = s₂ :=
  ext <| List.lt_antisymm' (α := Char)
    (fun h1 h2 => Char.le_antisymm (Nat.not_lt.1 h2) (Nat.not_lt.1 h1)) h₁ h₂

instance : Batteries.TransOrd String := .compareOfLessAndEq
  String.lt_irrefl String.lt_trans String.lt_antisymm

instance : Batteries.LTOrd String := .compareOfLessAndEq
  String.lt_irrefl String.lt_trans String.lt_antisymm

instance : Batteries.BEqOrd String := .compareOfLessAndEq String.lt_irrefl

@[simp] theorem mk_length (s : List Char) : (String.mk s).length = s.length := rfl

attribute [simp] toList -- prefer `String.data` over `String.toList` in lemmas

private theorem add_utf8Size_pos : 0 < i + Char.utf8Size c :=
  Nat.add_pos_right _ (Char.utf8Size_pos c)

private theorem ne_add_utf8Size_add_self : i ≠ n + Char.utf8Size c + i :=
  Nat.ne_of_lt (Nat.lt_add_of_pos_left add_utf8Size_pos)

private theorem ne_self_add_add_utf8Size : i ≠ i + (n + Char.utf8Size c) :=
  Nat.ne_of_lt (Nat.lt_add_of_pos_right add_utf8Size_pos)

/-- The UTF-8 byte length of a list of characters. (This is intended for specification purposes.) -/
@[inline] def utf8Len : List Char → Nat := utf8ByteSize.go

@[simp] theorem utf8ByteSize.go_eq : utf8ByteSize.go = utf8Len := rfl

@[simp] theorem utf8ByteSize_mk (cs) : utf8ByteSize ⟨cs⟩ = utf8Len cs := rfl

@[simp] theorem utf8Len_nil : utf8Len [] = 0 := rfl

@[simp] theorem utf8Len_cons (c cs) : utf8Len (c :: cs) = utf8Len cs + c.utf8Size := rfl

@[simp] theorem utf8Len_append (cs₁ cs₂) : utf8Len (cs₁ ++ cs₂) = utf8Len cs₁ + utf8Len cs₂ := by
  induction cs₁ <;> simp [*, Nat.add_right_comm]

@[simp] theorem utf8Len_reverseAux (cs₁ cs₂) :
    utf8Len (cs₁.reverseAux cs₂) = utf8Len cs₁ + utf8Len cs₂ := by
  induction cs₁ generalizing cs₂ <;> simp [*, ← Nat.add_assoc, Nat.add_right_comm]

@[simp] theorem utf8Len_reverse (cs) : utf8Len cs.reverse = utf8Len cs := utf8Len_reverseAux ..

@[simp] theorem utf8Len_eq_zero : utf8Len l = 0 ↔ l = [] := by
  cases l <;> simp [Nat.ne_of_gt add_utf8Size_pos]

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

@[simp] theorem endPos_eq (cs : List Char) : endPos ⟨cs⟩ = ⟨utf8Len cs⟩ := rfl

namespace Pos

-- TODO(kmill): add `@[ext]` attribute to `String.Pos.ext` in core.
attribute [ext (iff := false)] ext

theorem lt_addChar (p : Pos) (c : Char) : p < p + c := Nat.lt_add_of_pos_right (Char.utf8Size_pos _)

private theorem zero_ne_addChar {i : Pos} {c : Char} : 0 ≠ i + c :=
  ne_of_lt add_utf8Size_pos

/-- A string position is valid if it is equal to the UTF-8 length of an initial substring of `s`. -/
def Valid (s : String) (p : Pos) : Prop :=
  ∃ cs cs', cs ++ cs' = s.1 ∧ p.1 = utf8Len cs

@[simp] theorem valid_zero : Valid s 0 := ⟨[], s.1, rfl, rfl⟩

@[simp] theorem valid_endPos : Valid s (endPos s) := ⟨s.1, [], by simp, rfl⟩

theorem Valid.mk (cs cs' : List Char) : Valid ⟨cs ++ cs'⟩ ⟨utf8Len cs⟩ := ⟨cs, cs', rfl, rfl⟩

theorem Valid.le_endPos : ∀ {s p}, Valid s p → p ≤ endPos s
  | ⟨_⟩, ⟨_⟩, ⟨cs, cs', rfl, rfl⟩ => by simp [Nat.le_add_right]

end Pos

theorem endPos_eq_zero : ∀ (s : String), endPos s = 0 ↔ s = ""
  | ⟨_⟩ => Pos.ext_iff.trans <| utf8Len_eq_zero.trans ext_iff.symm

theorem isEmpty_iff (s : String) : isEmpty s ↔ s = "" :=
  (beq_iff_eq ..).trans (endPos_eq_zero _)

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
  simp only [utf8GetAux, Char.reduceDefault, implies_true, ↓reduceIte, ne_eq, pos_add_char]
  intro c cs ⟨i⟩ h ih
  simp only [Pos.ext_iff, Pos.addChar_eq] at h ⊢
  simp only [Nat.add_right_cancel_iff, h, ↓reduceIte]
  rw [Nat.add_right_comm]
  exact ih

theorem utf8GetAux_addChar_right_cancel (s : List Char) (i p : Pos) (c : Char) :
    utf8GetAux s (i + c) (p + c) = utf8GetAux s i p := utf8GetAux_add_right_cancel ..

theorem utf8GetAux_of_valid (cs cs' : List Char) {i p : Nat} (hp : i + utf8Len cs = p) :
    utf8GetAux (cs ++ cs') ⟨i⟩ ⟨p⟩ = cs'.headD default := by
  match cs, cs' with
  | [], [] => rfl
  | [], c::cs' => simp [← hp, utf8GetAux]
  | c::cs, cs' =>
    simp only [utf8GetAux, List.append_eq, Char.reduceDefault, ↓Char.isValue]
    rw [if_neg]
    case hnc => simp only [← hp, utf8Len_cons, Pos.ext_iff]; exact ne_self_add_add_utf8Size
    refine utf8GetAux_of_valid cs cs' ?_
    simpa [Nat.add_assoc, Nat.add_comm] using hp

theorem get_of_valid (cs cs' : List Char) : get ⟨cs ++ cs'⟩ ⟨utf8Len cs⟩ = cs'.headD default :=
  utf8GetAux_of_valid _ _ (Nat.zero_add _)

theorem get_cons_addChar (c : Char) (cs : List Char) (i : Pos) :
    get ⟨c :: cs⟩ (i + c) = get ⟨cs⟩ i := by
  simp [get, utf8GetAux, Pos.zero_ne_addChar, utf8GetAux_addChar_right_cancel]

theorem utf8GetAux?_of_valid (cs cs' : List Char) {i p : Nat} (hp : i + utf8Len cs = p) :
    utf8GetAux? (cs ++ cs') ⟨i⟩ ⟨p⟩ = cs'.head? := by
  match cs, cs' with
  | [], [] => rfl
  | [], c::cs' => simp [← hp, utf8GetAux?]
  | c::cs, cs' =>
    simp only [utf8GetAux?, List.append_eq]
    rw [if_neg]
    case hnc => simp [← hp, Pos.ext_iff]; exact ne_self_add_add_utf8Size
    refine utf8GetAux?_of_valid cs cs' ?_
    simpa [Nat.add_assoc, Nat.add_comm] using hp

theorem get?_of_valid (cs cs' : List Char) : get? ⟨cs ++ cs'⟩ ⟨utf8Len cs⟩ = cs'.head? :=
  utf8GetAux?_of_valid _ _ (Nat.zero_add _)

theorem utf8SetAux_of_valid (c' : Char) (cs cs' : List Char) {i p : Nat} (hp : i + utf8Len cs = p) :
    utf8SetAux c' (cs ++ cs') ⟨i⟩ ⟨p⟩ = cs ++ cs'.modifyHead fun _ => c' := by
  match cs, cs' with
  | [], [] => rfl
  | [], c::cs' => simp [← hp, utf8SetAux]
  | c::cs, cs' =>
    simp only [utf8SetAux, List.append_eq, List.cons_append]
    rw [if_neg]
    case hnc => simp [← hp, Pos.ext_iff]; exact ne_self_add_add_utf8Size
    refine congrArg (c::·) (utf8SetAux_of_valid c' cs cs' ?_)
    simpa [Nat.add_assoc, Nat.add_comm] using hp

theorem set_of_valid (cs cs' : List Char) (c' : Char) :
    set ⟨cs ++ cs'⟩ ⟨utf8Len cs⟩ c' = ⟨cs ++ cs'.modifyHead fun _ => c'⟩ :=
  ext (utf8SetAux_of_valid _ _ _ (Nat.zero_add _))

theorem modify_of_valid (cs cs' : List Char) :
    modify ⟨cs ++ cs'⟩ ⟨utf8Len cs⟩ f = ⟨cs ++ cs'.modifyHead f⟩ := by
  rw [modify, set_of_valid, get_of_valid]; cases cs' <;> rfl

theorem next_of_valid' (cs cs' : List Char) :
    next ⟨cs ++ cs'⟩ ⟨utf8Len cs⟩ = ⟨utf8Len cs + (cs'.headD default).utf8Size⟩ := by
  simp only [next, get_of_valid]; rfl

theorem next_of_valid (cs : List Char) (c : Char) (cs' : List Char) :
    next ⟨cs ++ c :: cs'⟩ ⟨utf8Len cs⟩ = ⟨utf8Len cs + c.utf8Size⟩ := next_of_valid' ..

@[simp] theorem atEnd_iff (s : String) (p : Pos) : atEnd s p ↔ s.endPos ≤ p :=
  decide_eq_true_iff _

theorem valid_next {p : Pos} (h : p.Valid s) (h₂ : p < s.endPos) : (next s p).Valid s := by
  match s, p, h with
  | ⟨_⟩, ⟨_⟩, ⟨cs, [], rfl, rfl⟩ => simp at h₂
  | ⟨_⟩, ⟨_⟩, ⟨cs, c::cs', rfl, rfl⟩ =>
    rw [utf8ByteSize.go_eq, next_of_valid]
    simpa using Pos.Valid.mk (cs ++ [c]) cs'

theorem utf8PrevAux_of_valid {cs cs' : List Char} {c : Char} {i p : Nat}
    (hp : i + (utf8Len cs + c.utf8Size) = p) :
    utf8PrevAux (cs ++ c :: cs') ⟨i⟩ ⟨p⟩ = ⟨i + utf8Len cs⟩ := by
  match cs with
  | [] => simp [utf8PrevAux, ← hp, Pos.addChar_eq]
  | c'::cs =>
    simp only [utf8PrevAux, Pos.addChar_eq, ← hp, utf8Len_cons, List.append_eq]
    rw [if_neg]
    case hnc =>
      simp only [Pos.ext_iff]
      rw [Nat.add_right_comm, Nat.add_left_comm]
      apply ne_add_utf8Size_add_self
    refine (utf8PrevAux_of_valid (by simp [Nat.add_assoc, Nat.add_left_comm])).trans ?_
    simp [Nat.add_assoc, Nat.add_comm]

theorem prev_of_valid (cs : List Char) (c : Char) (cs' : List Char) :
    prev ⟨cs ++ c :: cs'⟩ ⟨utf8Len cs + c.utf8Size⟩ = ⟨utf8Len cs⟩ := by
  simp only [prev]
  refine (if_neg (Pos.ne_of_gt add_utf8Size_pos)).trans ?_
  rw [utf8PrevAux_of_valid] <;> simp

theorem prev_of_valid' (cs cs' : List Char) :
    prev ⟨cs ++ cs'⟩ ⟨utf8Len cs⟩ = ⟨utf8Len cs.dropLast⟩ := by
  match cs, cs.eq_nil_or_concat with
  | _, .inl rfl => rfl
  | _, .inr ⟨cs, c, rfl⟩ => simp [prev_of_valid]

theorem front_eq (s : String) : front s = s.1.headD default := by
  unfold front; exact get_of_valid [] s.1

theorem back_eq (s : String) : back s = s.1.getLastD default := by
  match s, s.1.eq_nil_or_concat with
  | ⟨_⟩, .inl rfl => rfl
  | ⟨_⟩, .inr ⟨cs, c, rfl⟩ => simp [back, prev_of_valid, get_of_valid]

theorem atEnd_of_valid (cs : List Char) (cs' : List Char) :
    atEnd ⟨cs ++ cs'⟩ ⟨utf8Len cs⟩ ↔ cs' = [] := by
  rw [atEnd_iff]
  cases cs' <;> simp [Nat.lt_add_of_pos_right add_utf8Size_pos]

unseal posOfAux findAux in
theorem posOfAux_eq (s c) : posOfAux s c = findAux s (· == c) := rfl

unseal posOfAux findAux in
theorem posOf_eq (s c) : posOf s c = find s (· == c) := rfl

unseal revPosOfAux revFindAux in
theorem revPosOfAux_eq (s c) : revPosOfAux s c = revFindAux s (· == c) := rfl

unseal revPosOfAux revFindAux in
theorem revPosOf_eq (s c) : revPosOf s c = revFind s (· == c) := rfl

@[nolint unusedHavesSuffices] -- false positive from unfolding String.findAux
theorem findAux_of_valid (p) : ∀ l m r,
    findAux ⟨l ++ m ++ r⟩ p ⟨utf8Len l + utf8Len m⟩ ⟨utf8Len l⟩ =
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
      simp only [List.append_assoc, List.singleton_append, List.cons_append, utf8Len_append,
        utf8Len_cons, utf8Len_nil, Nat.zero_add, List.nil_append] at foo
      rw [Nat.add_right_comm, Nat.add_assoc] at foo
      rw [foo, Nat.add_right_comm, Nat.add_assoc]
    · simp

theorem find_of_valid (p s) : find s p = ⟨utf8Len (s.1.takeWhile (!p ·))⟩ := by
  simpa using findAux_of_valid p [] s.1 []

@[nolint unusedHavesSuffices] -- false positive from unfolding String.revFindAux
theorem revFindAux_of_valid (p) : ∀ l r,
    revFindAux ⟨l.reverse ++ r⟩ p ⟨utf8Len l⟩ = (l.dropWhile (!p ·)).tail?.map (⟨utf8Len ·⟩)
  | [], r => by unfold revFindAux List.dropWhile; simp
  | c::l, r => by
    unfold revFindAux List.dropWhile
    rw [dif_neg (by exact Pos.ne_of_gt add_utf8Size_pos)]
    have h1 := get_of_valid l.reverse (c::r); have h2 := prev_of_valid l.reverse c r
    simp only [utf8Len_reverse, Char.reduceDefault, List.headD_cons] at h1 h2
    simp only [List.reverse_cons, List.append_assoc, List.singleton_append, utf8Len_cons, h2, h1]
    cases p c <;> simp only [Bool.false_eq_true, ↓reduceIte, Bool.not_false, Bool.not_true,
      List.tail?_cons, Option.map_some']
    exact revFindAux_of_valid p l (c::r)

theorem revFind_of_valid (p s) :
    revFind s p = (s.1.reverse.dropWhile (!p ·)).tail?.map (⟨utf8Len ·⟩) := by
  simpa using revFindAux_of_valid p s.1.reverse []

theorem firstDiffPos_loop_eq (l₁ l₂ r₁ r₂ stop p)
    (hl₁ : p = utf8Len l₁) (hl₂ : p = utf8Len l₂)
    (hstop : stop = min (utf8Len l₁ + utf8Len r₁) (utf8Len l₂ + utf8Len r₂)) :
    firstDiffPos.loop ⟨l₁ ++ r₁⟩ ⟨l₂ ++ r₂⟩ ⟨stop⟩ ⟨p⟩ =
      ⟨p + utf8Len (List.takeWhile₂ (· = ·) r₁ r₂).1⟩ := by
  unfold List.takeWhile₂; split <;> unfold firstDiffPos.loop
  · next a r₁ b r₂ =>
    rw [
      dif_pos <| by
        rw [hstop, ← hl₁, ← hl₂]
        refine Nat.lt_min.2 ⟨?_, ?_⟩ <;> exact Nat.lt_add_of_pos_right add_utf8Size_pos,
      show get ⟨l₁ ++ a :: r₁⟩ ⟨p⟩ = a by simp [hl₁, get_of_valid],
      show get ⟨l₂ ++ b :: r₂⟩ ⟨p⟩ = b by simp [hl₂, get_of_valid]]
    simp only [bne_iff_ne, ne_eq, ite_not, decide_eq_true_eq]
    split
    · simp only [utf8Len_cons]
      subst b
      rw [show next ⟨l₁ ++ a :: r₁⟩ ⟨p⟩ = ⟨utf8Len l₁ + a.utf8Size⟩ by simp [hl₁, next_of_valid]]
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
    firstDiffPos a b = ⟨utf8Len (List.takeWhile₂ (· = ·) a.1 b.1).1⟩ := by
  simpa [firstDiffPos] using
    firstDiffPos_loop_eq [] [] a.1 b.1 ((utf8Len a.1).min (utf8Len b.1)) 0 rfl rfl (by simp)

theorem extract.go₂_add_right_cancel (s : List Char) (i e n : Nat) :
    go₂ s ⟨i + n⟩ ⟨e + n⟩ = go₂ s ⟨i⟩ ⟨e⟩ := by
  apply utf8InductionOn s ⟨i⟩ ⟨e⟩ (motive := fun s i =>
    go₂ s ⟨i.byteIdx + n⟩ ⟨e + n⟩ = go₂ s i ⟨e⟩)
    <;> simp only [ne_eq, go₂, pos_add_char, implies_true, ↓reduceIte]
  intro c cs ⟨i⟩ h ih
  simp only [Pos.ext_iff, Pos.addChar_eq] at h ⊢
  simp only [Nat.add_right_cancel_iff, h, ↓reduceIte, List.cons.injEq, true_and]
  rw [Nat.add_right_comm]
  exact ih

theorem extract.go₂_append_left : ∀ (s t : List Char) (i e : Nat),
    e = utf8Len s + i → go₂ (s ++ t) ⟨i⟩ ⟨e⟩ = s
| [], t, i, _, rfl => by cases t <;> simp [go₂]
| c :: cs, t, i, _, rfl => by
  simp only [go₂, utf8Len_cons, Pos.ext_iff, ne_add_utf8Size_add_self, ↓reduceIte, List.append_eq,
    Pos.addChar_eq, List.cons.injEq, true_and]
  apply go₂_append_left; rw [Nat.add_right_comm, Nat.add_assoc]

theorem extract.go₁_add_right_cancel (s : List Char) (i b e n : Nat) :
    go₁ s ⟨i + n⟩ ⟨b + n⟩ ⟨e + n⟩ = go₁ s ⟨i⟩ ⟨b⟩ ⟨e⟩ := by
  apply utf8InductionOn s ⟨i⟩ ⟨b⟩ (motive := fun s i =>
    go₁ s ⟨i.byteIdx + n⟩ ⟨b + n⟩ ⟨e + n⟩ = go₁ s i ⟨b⟩ ⟨e⟩)
    <;> simp only [ne_eq, go₁, pos_add_char, implies_true, ↓reduceIte]
  · intro c cs
    apply go₂_add_right_cancel
  · intro c cs ⟨i⟩ h ih
    simp only [Pos.ext_iff, Pos.addChar_eq] at h ih ⊢
    simp only [Nat.add_right_cancel_iff, h, ↓reduceIte]
    rw [Nat.add_right_comm]
    exact ih

theorem extract.go₁_cons_addChar (c : Char) (cs : List Char) (b e : Pos) :
    go₁ (c :: cs) 0 (b + c) (e + c) = go₁ cs 0 b e := by
  simp only [go₁, Pos.ext_iff, Pos.byteIdx_zero, pos_add_char, Nat.ne_of_lt add_utf8Size_pos,
    ↓reduceIte]
  apply go₁_add_right_cancel

theorem extract.go₁_append_right : ∀ (s t : List Char) (i b : Nat) (e : Pos),
    b = utf8Len s + i → go₁ (s ++ t) ⟨i⟩ ⟨b⟩ e = go₂ t ⟨b⟩ e
| [], t, i, _, e, rfl => by cases t <;> simp [go₁, go₂]
| c :: cs, t, i, _, e, rfl => by
  simp only [go₁, utf8Len_cons, Pos.ext_iff, ne_add_utf8Size_add_self, ↓reduceIte, List.append_eq,
    Pos.addChar_eq]
  apply go₁_append_right; rw [Nat.add_right_comm, Nat.add_assoc]

theorem extract.go₁_zero_utf8Len (s : List Char) : go₁ s 0 0 ⟨utf8Len s⟩ = s :=
  (go₁_append_right [] s 0 0 ⟨utf8Len s⟩ rfl).trans <| by
    simpa using go₂_append_left s [] 0 (utf8Len s) rfl

theorem extract_cons_addChar (c : Char) (cs : List Char) (b e : Pos) :
    extract ⟨c :: cs⟩ (b + c) (e + c) = extract ⟨cs⟩ b e := by
  simp only [extract, pos_add_char, ge_iff_le, Nat.add_le_add_iff_right]
  split <;> [rfl; rw [extract.go₁_cons_addChar]]

theorem extract_zero_endPos : ∀ (s : String), s.extract 0 (endPos s) = s
  | ⟨[]⟩ => rfl
  | ⟨c :: cs⟩ => by
    simp only [extract, Pos.byteIdx_zero, endPos_eq, utf8Len_cons, ge_iff_le, Nat.le_zero_eq,
      Nat.ne_of_gt add_utf8Size_pos, ↓reduceIte]
    congr
    apply extract.go₁_zero_utf8Len

theorem extract_of_valid (l m r : List Char) :
    extract ⟨l ++ m ++ r⟩ ⟨utf8Len l⟩ ⟨utf8Len l + utf8Len m⟩ = ⟨m⟩ := by
  simp only [extract]
  split
  · next h => rw [utf8Len_eq_zero.1 <| Nat.le_zero.1 <| Nat.add_le_add_iff_left.1 h]
  · congr; rw [List.append_assoc, extract.go₁_append_right _ _ _ _ _ (by rfl)]
    apply extract.go₂_append_left; apply Nat.add_comm

theorem splitAux_of_valid (p l m r acc) :
    splitAux ⟨l ++ m ++ r⟩ p ⟨utf8Len l⟩ ⟨utf8Len l + utf8Len m⟩ acc =
      acc.reverse ++ (List.splitOnP.go p r m.reverse).map mk := by
  unfold splitAux
  simp only [List.append_assoc, atEnd_iff, endPos_eq, utf8Len_append, Pos.mk_le_mk,
    Nat.add_le_add_iff_left, by simpa using atEnd_of_valid (l ++ m) r, List.reverse_cons,
    dite_eq_ite]
  split
  · subst r; simpa [List.splitOnP.go] using extract_of_valid l m []
  · obtain ⟨c, r, rfl⟩ := r.exists_cons_of_ne_nil ‹_›
    simp only [by
      simpa using
        (⟨get_of_valid (l ++ m) (c :: r), next_of_valid (l ++ m) c r,
            extract_of_valid l m (c :: r)⟩ :
          _ ∧ _ ∧ _),
      List.splitOnP.go, List.reverse_reverse]
    split
    · simpa [Nat.add_assoc] using splitAux_of_valid p (l++m++[c]) [] r (⟨m⟩::acc)
    · simpa [Nat.add_assoc] using splitAux_of_valid p l (m++[c]) r acc

theorem split_of_valid (s p) : split s p = (List.splitOnP p s.1).map mk := by
  simpa [split] using splitAux_of_valid p [] [] s.1 []

-- TODO: splitOn

@[simp] theorem toString_toSubstring (s : String) : s.toSubstring.toString = s :=
  extract_zero_endPos _

attribute [simp] toSubstring'

theorem join_eq (ss : List String) : join ss = ⟨(ss.map data).join⟩ := go ss [] where
  go : ∀ (ss : List String) cs, ss.foldl (· ++ ·) (mk cs) = ⟨cs ++ (ss.map data).join⟩
    | [], _ => by simp
    | ⟨s⟩::ss, _ => (go ss _).trans (by simp)

@[simp] theorem data_join (ss : List String) : (join ss).data = (ss.map data).join := by
  rw [join_eq]

@[deprecated (since := "2024-06-06")] alias append_nil := append_empty
@[deprecated (since := "2024-06-06")] alias nil_append := empty_append

namespace Iterator

@[simp] theorem forward_eq_nextn : forward = nextn := by
  funext it n; induction n generalizing it <;> simp [forward, nextn, *]

theorem hasNext_cons_addChar (c : Char) (cs : List Char) (i : Pos) :
    hasNext ⟨⟨c :: cs⟩, i + c⟩ = hasNext ⟨⟨cs⟩, i⟩ := by
  simp [hasNext, Nat.add_lt_add_iff_right]

/-- Validity for a string iterator. -/
def Valid (it : Iterator) : Prop := it.pos.Valid it.s

/-- `it.ValidFor l r` means that `it` is a string iterator whose underlying string is
`l.reverse ++ r`, and where the cursor is pointing at the end of `l.reverse`. -/
inductive ValidFor (l r : List Char) : Iterator → Prop
  /-- The canonical constructor for `ValidFor`. -/
  | mk : ValidFor l r ⟨⟨l.reverseAux r⟩, ⟨utf8Len l⟩⟩

attribute [simp] toString pos

namespace ValidFor

theorem valid : ∀ {it}, ValidFor l r it → Valid it
  | _, ⟨⟩ => by simpa [List.reverseAux_eq] using Pos.Valid.mk l.reverse r

theorem out : ∀ {it}, ValidFor l r it → it = ⟨⟨l.reverseAux r⟩, ⟨utf8Len l⟩⟩
  | _, ⟨⟩ => rfl

theorem out' : ∀ {it}, ValidFor l r it → it = ⟨⟨l.reverse ++ r⟩, ⟨utf8Len l.reverse⟩⟩
  | _, ⟨⟩ => by simp [List.reverseAux_eq]

theorem mk' : ValidFor l r ⟨⟨l.reverse ++ r⟩, ⟨utf8Len l.reverse⟩⟩ := by
  simpa [List.reverseAux_eq] using mk

theorem of_eq : ∀ it, it.1.1 = l.reverseAux r → it.2.1 = utf8Len l → ValidFor l r it
  | ⟨⟨_⟩, ⟨_⟩⟩, rfl, rfl => ⟨⟩

theorem _root_.String.validFor_mkIterator (s) : (mkIterator s).ValidFor [] s.1 := ⟨⟩

theorem remainingBytes : ∀ {it}, ValidFor l r it → it.remainingBytes = utf8Len r
  | _, ⟨⟩ => by simp [Iterator.remainingBytes, Nat.add_sub_cancel_left]

theorem toString : ∀ {it}, ValidFor l r it → it.1 = ⟨l.reverseAux r⟩
  | _, ⟨⟩ => rfl

theorem pos : ∀ {it}, ValidFor l r it → it.2 = ⟨utf8Len l⟩
  | _, ⟨⟩ => rfl

theorem pos_eq_zero {l r it} (h : ValidFor l r it) : it.2 = 0 ↔ l = [] := by
  simp [h.pos, Pos.ext_iff]

theorem pos_eq_endPos {l r it} (h : ValidFor l r it) : it.2 = it.1.endPos ↔ r = [] := by
  simp only [h.pos, h.toString, endPos_eq, utf8Len_reverseAux, Pos.ext_iff]
  exact (Nat.add_left_cancel_iff (m := 0)).trans <| eq_comm.trans utf8Len_eq_zero

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
      Pos.mk_zero, prev_zero]
    constructor

theorem atEnd : ∀ {it}, ValidFor l r it → (it.atEnd ↔ r = [])
  | it, h => by
    simp only [Iterator.atEnd, h.pos, h.toString, endPos_eq, utf8Len_reverseAux, ge_iff_le,
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
    simp only [utf8Len_reverse] at this; simp [List.reverseAux_eq, this]

theorem setCurr (h : ValidFor l (c :: r) it) :
    ValidFor l (c :: r) (it.setCurr c) := h.setCurr'

theorem toEnd (h : ValidFor l r it) : ValidFor (r.reverse ++ l) [] it.toEnd := by
  simp only [Iterator.toEnd, h.toString, endPos_eq, utf8Len_reverseAux]
  exact .of_eq _ (by simp [List.reverseAux_eq]) (by simp [Nat.add_comm])

theorem toEnd' (it : Iterator) : ValidFor it.s.1.reverse [] it.toEnd := by
  simp only [Iterator.toEnd]
  exact .of_eq _ (by simp [List.reverseAux_eq]) (by simp [endPos, utf8ByteSize])

theorem extract (h₁ : ValidFor l (m ++ r) it₁) (h₂ : ValidFor (m.reverse ++ l) r it₂) :
    it₁.extract it₂ = ⟨m⟩ := by
  cases h₁.out; cases h₂.out
  simp only [Iterator.extract, List.reverseAux_eq, List.reverse_append, List.reverse_reverse,
    List.append_assoc, ne_eq, not_true_eq_false, decide_False, utf8Len_append, utf8Len_reverse,
    gt_iff_lt, pos_lt_eq, Nat.not_lt.2 (Nat.le_add_left ..), Bool.or_self, Bool.false_eq_true,
    ↓reduceIte]
  simpa [Nat.add_comm] using extract_of_valid l.reverse m r

theorem remainingToString {it} (h : ValidFor l r it) : it.remainingToString = ⟨r⟩ := by
  cases h.out
  simpa [Iterator.remainingToString, List.reverseAux_eq] using extract_of_valid l.reverse r []

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
  | ⟨⟨_⟩, ⟨_⟩⟩, ⟨l, r, rfl, rfl⟩ =>
    ⟨l.reverse, r, by simpa [List.reverseAux_eq] using @ValidFor.mk l.reverse r⟩

theorem _root_.String.valid_mkIterator (s) : (mkIterator s).Valid := s.validFor_mkIterator.valid

theorem remainingBytes_le : ∀ {it}, Valid it → it.remainingBytes ≤ utf8ByteSize it.s
  | _, h => let ⟨l, r, h⟩ := h.validFor; by simp [h.remainingBytes, h.toString, Nat.le_add_left]

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

theorem remainingToString {it} (h : ValidFor l r it) : it.remainingToString = ⟨r⟩ := by
  cases h.out
  simpa [Iterator.remainingToString, List.reverseAux_eq] using extract_of_valid l.reverse r []

theorem prevn (h : Valid it) : ∀ n, Valid (it.prevn n)
  | 0 => h
  | n+1 => h.prev.prevn n

end Valid
end Iterator

@[nolint unusedHavesSuffices] -- false positive from unfolding String.offsetOfPosAux
theorem offsetOfPosAux_of_valid : ∀ l m r n,
    offsetOfPosAux ⟨l ++ m ++ r⟩ ⟨utf8Len l + utf8Len m⟩ ⟨utf8Len l⟩ n = n + m.length
  | l, [], r, n => by unfold offsetOfPosAux; simp
  | l, c::m, r, n => by
    unfold offsetOfPosAux
    rw [if_neg (by exact Nat.not_le.2 (Nat.lt_add_of_pos_right add_utf8Size_pos))]
    simp only [List.append_assoc, atEnd_of_valid l (c::m++r)]
    simp only [List.cons_append, utf8Len_cons, next_of_valid l c (m ++ r)]
    simpa [← Nat.add_assoc, Nat.add_right_comm] using
      offsetOfPosAux_of_valid (l++[c]) m r (n + 1)

theorem offsetOfPos_of_valid (l r) : offsetOfPos ⟨l ++ r⟩ ⟨utf8Len l⟩ = l.length := by
  simpa using offsetOfPosAux_of_valid [] l r 0

@[nolint unusedHavesSuffices] -- false positive from unfolding String.foldlAux
theorem foldlAux_of_valid (f : α → Char → α) : ∀ l m r a,
    foldlAux f ⟨l ++ m ++ r⟩ ⟨utf8Len l + utf8Len m⟩ ⟨utf8Len l⟩ a = m.foldl f a
  | l, [], r, a => by unfold foldlAux; simp
  | l, c::m, r, a => by
    unfold foldlAux
    rw [dif_pos (by exact Nat.lt_add_of_pos_right add_utf8Size_pos)]
    simp only [List.append_assoc, List.cons_append, utf8Len_cons, next_of_valid l c (m ++ r),
      get_of_valid l (c :: (m ++ r)), Char.reduceDefault, List.headD_cons, List.foldl_cons]
    simpa [← Nat.add_assoc, Nat.add_right_comm] using foldlAux_of_valid f (l++[c]) m r (f a c)

theorem foldl_eq (f : α → Char → α) (s a) : foldl f a s = s.1.foldl f a := by
  simpa using foldlAux_of_valid f [] s.1 [] a

@[nolint unusedHavesSuffices] -- false positive from unfolding String.foldrAux
theorem foldrAux_of_valid (f : Char → α → α) (l m r a) :
    foldrAux f a ⟨l ++ m ++ r⟩ ⟨utf8Len l + utf8Len m⟩ ⟨utf8Len l⟩ = m.foldr f a := by
  rw [← m.reverse_reverse]
  induction m.reverse generalizing r a with (unfold foldrAux; simp)
  | cons c m IH =>
    rw [if_pos add_utf8Size_pos]
    simp only [← Nat.add_assoc, by simpa using prev_of_valid (l ++ m.reverse) c r]
    simp only [by simpa using get_of_valid (l ++ m.reverse) (c :: r)]
    simpa using IH (c::r) (f c a)

theorem foldr_eq (f : Char → α → α) (s a) : foldr f a s = s.1.foldr f a := by
  simpa using foldrAux_of_valid f [] s.1 [] a

@[nolint unusedHavesSuffices] -- false positive from unfolding String.anyAux
theorem anyAux_of_valid (p : Char → Bool) : ∀ l m r,
    anyAux ⟨l ++ m ++ r⟩ ⟨utf8Len l + utf8Len m⟩ p ⟨utf8Len l⟩ = m.any p
  | l, [], r => by unfold anyAux; simp
  | l, c::m, r => by
    unfold anyAux
    rw [dif_pos (by exact Nat.lt_add_of_pos_right add_utf8Size_pos)]
    simp only [List.append_assoc, List.cons_append, get_of_valid l (c :: (m ++ r)),
      Char.reduceDefault, List.headD_cons, utf8Len_cons, next_of_valid l c (m ++ r),
      Bool.if_true_left, Bool.decide_eq_true, List.any_cons]
    cases p c <;> simp
    simpa [← Nat.add_assoc, Nat.add_right_comm] using anyAux_of_valid p (l++[c]) m r

theorem any_eq (s : String) (p : Char → Bool) : any s p = s.1.any p := by
  simpa using anyAux_of_valid p [] s.1 []

theorem any_iff (s : String) (p : Char → Bool) : any s p ↔ ∃ c ∈ s.1, p c := by simp [any_eq]

theorem all_eq (s : String) (p : Char → Bool) : all s p = s.1.all p := by
  rw [all, any_eq, List.all_eq_not_any_not]

theorem all_iff (s : String) (p : Char → Bool) : all s p ↔ ∀ c ∈ s.1, p c := by simp [all_eq]

theorem contains_iff (s : String) (c : Char) : contains s c ↔ c ∈ s.1 := by
  simp [contains, any_iff]

@[nolint unusedHavesSuffices] -- false positive from unfolding String.mapAux
theorem mapAux_of_valid (f : Char → Char) : ∀ l r, mapAux f ⟨utf8Len l⟩ ⟨l ++ r⟩ = ⟨l ++ r.map f⟩
  | l, [] => by unfold mapAux; simp
  | l, c::r => by
    unfold mapAux
    rw [dif_neg (by rw [atEnd_of_valid]; simp)]
    simp only [get_of_valid l (c :: r), Char.reduceDefault, List.headD_cons,
      set_of_valid l (c :: r), List.modifyHead_cons, next_of_valid l (f c) r, List.map_cons]
    simpa using mapAux_of_valid f (l++[f c]) r

theorem map_eq (f : Char → Char) (s) : map f s = ⟨s.1.map f⟩ := by
  simpa using mapAux_of_valid f [] s.1

-- TODO: substrEq
-- TODO: isPrefixOf
-- TODO: replace

@[nolint unusedHavesSuffices] -- false positive from unfolding String.takeWhileAux
theorem takeWhileAux_of_valid (p : Char → Bool) : ∀ l m r,
    Substring.takeWhileAux ⟨l ++ m ++ r⟩ ⟨utf8Len l + utf8Len m⟩ p ⟨utf8Len l⟩ =
      ⟨utf8Len l + utf8Len (m.takeWhile p)⟩
  | l, [], r => by unfold Substring.takeWhileAux List.takeWhile; simp
  | l, c::m, r => by
    unfold Substring.takeWhileAux List.takeWhile
    rw [dif_pos (by exact Nat.lt_add_of_pos_right add_utf8Size_pos)]
    simp only [List.append_assoc, List.cons_append, get_of_valid l (c :: (m ++ r)),
      Char.reduceDefault, List.headD_cons, utf8Len_cons, next_of_valid l c (m ++ r)]
    cases p c <;> simp
    simpa [← Nat.add_assoc, Nat.add_right_comm] using takeWhileAux_of_valid p (l++[c]) m r

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

theorem Valid_default : Valid default := ⟨Pos.valid_zero, Pos.valid_zero, Nat.le_refl _⟩

/-- A substring is represented by three lists `l m r`, where `m` is the middle section
(the actual substring) and `l ++ m ++ r` is the underlying string. -/
inductive ValidFor (l m r : List Char) : Substring → Prop
  /-- The constructor for `ValidFor`. -/
  | mk : ValidFor l m r ⟨⟨l ++ m ++ r⟩, ⟨utf8Len l⟩, ⟨utf8Len l + utf8Len m⟩⟩

namespace ValidFor

theorem valid : ∀ {s}, ValidFor l m r s → Valid s
  | _, ⟨⟩ => ⟨⟨l, m ++ r, by simp⟩, ⟨l ++ m, r, by simp⟩, Nat.le_add_right ..⟩

theorem of_eq : ∀ s,
    s.str.1 = l ++ m ++ r →
    s.startPos.1 = utf8Len l →
    s.stopPos.1 = utf8Len l + utf8Len m →
    ValidFor l m r s
  | ⟨⟨_⟩, ⟨_⟩, ⟨_⟩⟩, rfl, rfl, rfl => ⟨⟩

theorem _root_.String.validFor_toSubstring (s : String) : ValidFor [] s.1 [] s :=
  .of_eq _ (by simp [toSubstring]) rfl (by simp [toSubstring, endPos, utf8ByteSize])

theorem str : ∀ {s}, ValidFor l m r s → s.str = ⟨l ++ m ++ r⟩
  | _, ⟨⟩ => rfl

theorem startPos : ∀ {s}, ValidFor l m r s → s.startPos = ⟨utf8Len l⟩
  | _, ⟨⟩ => rfl

theorem stopPos : ∀ {s}, ValidFor l m r s → s.stopPos = ⟨utf8Len l + utf8Len m⟩
  | _, ⟨⟩ => rfl

theorem bsize : ∀ {s}, ValidFor l m r s → s.bsize = utf8Len m
  | _, ⟨⟩ => by simp [Substring.bsize, Nat.add_sub_cancel_left]

theorem isEmpty : ∀ {s}, ValidFor l m r s → (s.isEmpty ↔ m = [])
  | _, h => by simp [Substring.isEmpty, h.bsize]

theorem toString : ∀ {s}, ValidFor l m r s → s.toString = ⟨m⟩
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
    rw [if_neg (mt Pos.ext_iff.1 ?a)]
    case a =>
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        @ne_add_utf8Size_add_self (utf8Len l + utf8Len m₁) (utf8Len m₂) c
    have := next_of_valid (l ++ m₁) c (m₂ ++ r)
    simp only [List.append_assoc, utf8Len_append, Pos.add_eq] at this ⊢; rw [this]
    simp [Nat.add_assoc, Nat.add_sub_cancel_left]

theorem next_stop : ∀ {s}, ValidFor l m r s → s.next ⟨utf8Len m⟩ = ⟨utf8Len m⟩
  | _, ⟨⟩ => by simp [Substring.next, Pos.add_eq]

theorem prev : ∀ {s}, ValidFor l (m₁ ++ c :: m₂) r s →
    s.prev ⟨utf8Len m₁ + c.utf8Size⟩ = ⟨utf8Len m₁⟩
  | _, ⟨⟩ => by
    simp only [Substring.prev, List.append_assoc, List.cons_append]
    rw [if_neg (mt Pos.ext_iff.1 <| Ne.symm ?a)]
    case a => simpa [Nat.add_comm] using @ne_add_utf8Size_add_self (utf8Len l) (utf8Len m₁) c
    have := prev_of_valid (l ++ m₁) c (m₂ ++ r)
    simp only [List.append_assoc, utf8Len_append, Nat.add_assoc, Pos.add_eq] at this ⊢; rw [this]
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

theorem drop : ∀ {s}, ValidFor l m r s → ∀ n, ValidFor (l ++ m.take n) (m.drop n) r (s.drop n)
  | s, h, n => by
    have : Substring.nextn {..} .. = _ := h.nextn (m₁ := []) n
    simp only [utf8Len_nil, Pos.mk_zero, Nat.zero_add] at this
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
    simp [-List.take_append_drop, Nat.add_assoc]

-- TODO: takeRight, dropRight

theorem atEnd : ∀ {s}, ValidFor l m r s → (s.atEnd ⟨p⟩ ↔ p = utf8Len m)
  | _, ⟨⟩ => by simp [Substring.atEnd, Pos.ext_iff, Nat.add_left_cancel_iff]

theorem extract : ∀ {s}, ValidFor l m r s → ValidFor ml mm mr ⟨⟨m⟩, b, e⟩ →
    ∃ l' r', ValidFor l' mm r' (s.extract b e)
  | _, ⟨⟩, ⟨⟩ => by
    simp only [Substring.extract, ge_iff_le, Pos.mk_le_mk, List.append_assoc, utf8Len_append]
    split
    · next h =>
      rw [utf8Len_eq_zero.1 <| Nat.le_zero.1 <| Nat.add_le_add_iff_left.1 h]
      exact ⟨[], [], ⟨⟩⟩
    · next h =>
      refine ⟨l ++ ml, mr ++ r, .of_eq _ (by simp) ?_ ?_⟩ <;>
        simp only [Pos.add_byteIdx, Nat.min_eq_min, utf8Len_append]
          <;> rw [Nat.min_eq_right]
          <;> try simp [Nat.add_le_add_iff_left, Nat.le_add_right]
      rw [Nat.add_assoc]

-- TODO: splitOn

theorem foldl (f) (init : α) : ∀ {s}, ValidFor l m r s → s.foldl f init = m.foldl f init
  | _, ⟨⟩ => by simp [-List.append_assoc, Substring.foldl, foldlAux_of_valid]

theorem foldr (f) (init : α) : ∀ {s}, ValidFor l m r s → s.foldr f init = m.foldr f init
  | _, ⟨⟩ => by simp [-List.append_assoc, Substring.foldr, foldrAux_of_valid]

theorem any (f) : ∀ {s}, ValidFor l m r s → s.any f = m.any f
  | _, ⟨⟩ => by simp [-List.append_assoc, Substring.any, anyAux_of_valid]

theorem all (f) : ∀ {s}, ValidFor l m r s → s.all f = m.all f
  | _, h => by simp [Substring.all, h.any, List.all_eq_not_any_not]

theorem contains (c) : ∀ {s}, ValidFor l m r s → (s.contains c ↔ c ∈ m)
  | _, h => by simp [Substring.contains, h.any, String.contains]

theorem takeWhile (p : Char → Bool) : ∀ {s}, ValidFor l m r s →
    ValidFor l (m.takeWhile p) (m.dropWhile p ++ r) (s.takeWhile p)
  | _, ⟨⟩ => by
    simp only [Substring.takeWhile, takeWhileAux_of_valid]
    refine' .of_eq .. <;> simp
    rw [← List.append_assoc, List.takeWhile_append_dropWhile]

theorem dropWhile (p : Char → Bool) : ∀ {s}, ValidFor l m r s →
    ValidFor (l ++ m.takeWhile p) (m.dropWhile p) r (s.dropWhile p)
  | _, ⟨⟩ => by
    simp only [Substring.dropWhile, takeWhileAux_of_valid]
    refine' .of_eq .. <;> simp
    rw [Nat.add_assoc, ← utf8Len_append (m.takeWhile p), List.takeWhile_append_dropWhile]

-- TODO: takeRightWhile

end ValidFor

namespace Valid

theorem validFor : ∀ {s}, Valid s → ∃ l m r, ValidFor l m r s
  | ⟨⟨_⟩, ⟨_⟩, ⟨_⟩⟩, ⟨⟨l, mr, rfl, rfl⟩, ⟨lm, r, e, rfl⟩, h⟩ => by
    simp only [utf8ByteSize.go_eq, Pos.mk_le_mk] at *
    have := (or_iff_right_iff_imp.2 fun h => ?x).1 (List.append_eq_append_iff.1 e)
    case x =>
      match l, r, h with | _, _, ⟨m, rfl, rfl⟩ => ?_
      simp only [utf8Len_append] at h
      cases utf8Len_eq_zero.1 <| Nat.le_zero.1 (Nat.le_of_add_le_add_left (c := 0) h)
      exact ⟨[], by simp⟩
    match lm, mr, this with
    | _, _, ⟨m, rfl, rfl⟩ => exact ⟨l, m, r, by simpa using ValidFor.mk⟩

theorem valid : ∀ {s}, ValidFor l m r s → Valid s
  | _, ⟨⟩ => ⟨⟨l, m ++ r, by simp⟩, ⟨l ++ m, r, by simp⟩, Nat.le_add_right ..⟩

theorem _root_.String.valid_toSubstring (s : String) : Valid s :=
  s.validFor_toSubstring.valid

theorem bsize : ∀ {s}, Valid s → s.bsize = utf8Len s.toString.1
  | _, h => let ⟨l, m, r, h⟩ := h.validFor; by simp [h.bsize, h.toString]

theorem isEmpty : ∀ {s}, Valid s → (s.isEmpty ↔ s.toString = "")
  | _, h => let ⟨l, m, r, h⟩ := h.validFor; by simp [h.isEmpty, h.toString, ext_iff]

theorem get : ∀ {s}, Valid s → s.toString.1 = m₁ ++ c :: m₂ → s.get ⟨utf8Len m₁⟩ = c
  | _, h, e => by
    let ⟨l, m, r, h⟩ := h.validFor
    simp only [h.toString] at e; subst e; simp [h.get]

theorem next : ∀ {s}, Valid s → s.toString.1 = m₁ ++ c :: m₂ →
    s.next ⟨utf8Len m₁⟩ = ⟨utf8Len m₁ + c.utf8Size⟩
  | _, h, e => by
    let ⟨l, m, r, h⟩ := h.validFor
    simp only [h.toString] at e; subst e; simp [h.next]

theorem next_stop : ∀ {s}, Valid s → s.next ⟨s.bsize⟩ = ⟨s.bsize⟩
  | _, h => let ⟨l, m, r, h⟩ := h.validFor; by simp [h.bsize, h.next_stop]

theorem prev : ∀ {s}, Valid s → s.toString.1 = m₁ ++ c :: m₂ →
    s.prev ⟨utf8Len m₁ + c.utf8Size⟩ = ⟨utf8Len m₁⟩
  | _, h, e => by
    let ⟨l, m, r, h⟩ := h.validFor
    simp only [h.toString] at e; subst e; simp [h.prev]

theorem nextn_stop : ∀ {s}, Valid s → ∀ n, s.nextn n ⟨s.bsize⟩ = ⟨s.bsize⟩
  | _, h, n => let ⟨l, m, r, h⟩ := h.validFor; by simp [h.bsize, h.nextn_stop]

theorem nextn : ∀ {s}, Valid s → s.toString.1 = m₁ ++ m₂ →
    ∀ n, s.nextn n ⟨utf8Len m₁⟩ = ⟨utf8Len m₁ + utf8Len (m₂.take n)⟩
  | _, h, e => by
    let ⟨l, m, r, h⟩ := h.validFor
    simp only [h.toString] at e; subst e; simp [h.nextn]

theorem prevn : ∀ {s}, Valid s → s.toString.1 = m₁.reverse ++ m₂ →
    ∀ n, s.prevn n ⟨utf8Len m₁⟩ = ⟨utf8Len (m₁.drop n)⟩
  | _, h, e => by
    let ⟨l, m, r, h⟩ := h.validFor
    simp only [h.toString] at e; subst e; simp [h.prevn]

theorem front : ∀ {s}, Valid s → s.toString.1 = c :: m → s.front = c
  | _, h => h.get (m₁ := [])

theorem drop : ∀ {s}, Valid s → ∀ n, Valid (s.drop n)
  | _, h, _ => let ⟨_, _, _, h⟩ := h.validFor; (h.drop _).valid

theorem data_drop : ∀ {s}, Valid s → ∀ n, (s.drop n).toString.1 = s.toString.1.drop n
  | _, h, _ => let ⟨_, _, _, h⟩ := h.validFor; by simp [(h.drop _).toString, h.toString]

theorem take : ∀ {s}, Valid s → ∀ n, Valid (s.take n)
  | _, h, _ => let ⟨_, _, _, h⟩ := h.validFor; (h.take _).valid

theorem data_take : ∀ {s}, Valid s → ∀ n, (s.take n).toString.1 = s.toString.1.take n
  | _, h, _ => let ⟨_, _, _, h⟩ := h.validFor; by simp [(h.take _).toString, h.toString]

-- TODO: takeRight, dropRight

theorem atEnd : ∀ {s}, Valid s → (s.atEnd ⟨p⟩ ↔ p = utf8ByteSize s.toString)
  | _, h => let ⟨_, _, _, h⟩ := h.validFor; by simp [h.atEnd, h.toString]

theorem extract : ∀ {s}, Valid s → Valid ⟨s.toString, b, e⟩ → Valid (s.extract b e)
  | _, h₁, h₂ => by
    let ⟨l, m, r, h₁⟩ := h₁.validFor
    rw [h₁.toString] at h₂
    let ⟨ml, mm, mr, h₂⟩ := h₂.validFor
    have ⟨l', r', h₃⟩ := h₁.extract h₂
    exact h₃.valid

theorem toString_extract : ∀ {s}, Valid s → Valid ⟨s.toString, b, e⟩ →
    (s.extract b e).toString = s.toString.extract b e
  | _, h₁, h₂ => by
    let ⟨l, m, r, h₁⟩ := h₁.validFor
    rw [h₁.toString] at h₂
    let ⟨ml, mm, mr, h₂⟩ := h₂.validFor
    have ⟨l', r', h₃⟩ := h₁.extract h₂
    rw [h₃.toString, h₁.toString, ← h₂.toString, toString]

theorem foldl (f) (init : α) : ∀ {s}, Valid s → s.foldl f init = s.toString.1.foldl f init
  | _, h => let ⟨_, _, _, h⟩ := h.validFor; by simp [h.foldl, h.toString]

theorem foldr (f) (init : α) : ∀ {s}, Valid s → s.foldr f init = s.toString.1.foldr f init
  | _, h => let ⟨_, _, _, h⟩ := h.validFor; by simp [h.foldr, h.toString]

theorem any (f) : ∀ {s}, Valid s → s.any f = s.toString.1.any f
  | _, h => let ⟨_, _, _, h⟩ := h.validFor; by simp [h.any, h.toString]

theorem all (f) : ∀ {s}, Valid s → s.all f = s.toString.1.all f
  | _, h => let ⟨_, _, _, h⟩ := h.validFor; by simp [h.all, h.toString]

theorem contains (c) : ∀ {s}, Valid s → (s.contains c ↔ c ∈ s.toString.1)
  | _, h => let ⟨_, _, _, h⟩ := h.validFor; by simp [h.contains, h.toString]

theorem takeWhile (p : Char → Bool) : ∀ {s}, Valid s → Valid (s.takeWhile p)
  | _, h => let ⟨_, _, _, h⟩ := h.validFor; (h.takeWhile _).valid

theorem data_takeWhile (p) : ∀ {s}, Valid s →
    (s.takeWhile p).toString.1 = s.toString.1.takeWhile p
  | _, h => let ⟨_, _, _, h⟩ := h.validFor; by simp [(h.takeWhile _).toString, h.toString]

theorem dropWhile (p : Char → Bool) : ∀ {s}, Valid s → Valid (s.dropWhile p)
  | _, h => let ⟨_, _, _, h⟩ := h.validFor; (h.dropWhile _).valid

theorem data_dropWhile (p) : ∀ {s}, Valid s →
    (s.dropWhile p).toString.1 = s.toString.1.dropWhile p
  | _, h => let ⟨_, _, _, h⟩ := h.validFor; by simp [(h.dropWhile _).toString, h.toString]

-- TODO: takeRightWhile

end Valid
end Substring

namespace String

theorem drop_eq (s : String) (n : Nat) : s.drop n = ⟨s.1.drop n⟩ :=
  (s.validFor_toSubstring.drop n).toString

@[simp] theorem data_drop (s : String) (n : Nat) : (s.drop n).1 = s.1.drop n := by rw [drop_eq]

@[simp] theorem drop_empty {n : Nat} : "".drop n = "" := by rw [drop_eq, List.drop_nil]

theorem take_eq (s : String) (n : Nat) : s.take n = ⟨s.1.take n⟩ :=
  (s.validFor_toSubstring.take n).toString

@[simp] theorem data_take (s : String) (n : Nat) : (s.take n).1 = s.1.take n := by rw [take_eq]

theorem takeWhile_eq (p : Char → Bool) (s : String) : s.takeWhile p = ⟨s.1.takeWhile p⟩ :=
  (s.validFor_toSubstring.takeWhile p).toString

@[simp] theorem data_takeWhile (p : Char → Bool) (s : String) :
    (s.takeWhile p).1 = s.1.takeWhile p := by rw [takeWhile_eq]

theorem dropWhile_eq (p : Char → Bool) (s : String) : s.dropWhile p = ⟨s.1.dropWhile p⟩ :=
  (s.validFor_toSubstring.dropWhile p).toString

@[simp] theorem data_dropWhile (p : Char → Bool) (s : String) :
    (s.dropWhile p).1 = s.1.dropWhile p := by rw [dropWhile_eq]

end String

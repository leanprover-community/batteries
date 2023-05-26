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
          Nat.add_le_add (Nat.le_of_lt $ Nat.not_le.mp h) (String.csize_le_4 _)
        have : stop.byteIdx + 4 - (start.byteIdx + String.csize cs) <
                stop.byteIdx + 4 - start.byteIdx :=
          Nat.sub_add_lt_sub this (String.csize_pos _)
        go (start + cs) stop
      else
        none
termination_by go start stop => stop.byteIdx + 4 - start.byteIdx

end Substring

namespace String

/--
If `pre` is a prefix of `s`, i.e. `s = pre ++ t`, return the remainder `t`.
-/
def dropPrefix? (s : String) (pre : String) : Option Substring :=
  s.toSubstring.dropPrefix? pre.toSubstring

end String

/-! # non-partial definitions from lean4#2214

FIXME: remove this once it lands
-/

section deleteme
set_option linter.missingDocs false

namespace String

theorem utf8PrevAux_lt_of_pos : ∀ (cs : List Char) (i p : Pos), p ≠ 0 →
    (utf8PrevAux cs i p).1 < p.1
  | [], i, p, h =>
    Nat.lt_of_le_of_lt (Nat.zero_le _)
      (Nat.zero_lt_of_ne_zero (mt (congrArg Pos.mk) h))
  | c::cs, i, p, h => by
    simp [utf8PrevAux]; split
    next h' => exact h' ▸ Nat.add_lt_add_left (one_le_csize _) _
    next => exact utf8PrevAux_lt_of_pos _ _ _ h

theorem prev_lt_of_pos (s : String) (i : Pos) (h : i ≠ 0) : (s.prev i).1 < i.1 := by
  simp [prev, h]
  exact utf8PrevAux_lt_of_pos _ _ _ h

def posOfAuxWF (s : String) (c : Char) (stopPos : Pos) (pos : Pos) : Pos :=
  if h : pos < stopPos then
    if s.get pos == c then pos
    else
      have := Nat.sub_lt_sub_left h (lt_next s pos)
      posOfAuxWF s c stopPos (s.next pos)
  else pos
termination_by _ => stopPos.1 - pos.1

@[inline] def posOfWF (s : String) (c : Char) : Pos :=
  posOfAuxWF s c s.endPos 0

def revPosOfAuxWF (s : String) (c : Char) (pos : Pos) : Option Pos :=
  if h : pos = 0 then none
  else
    have := prev_lt_of_pos s pos h
    let pos := s.prev pos
    if s.get pos == c then some pos
    else revPosOfAuxWF s c pos
termination_by _ => pos.1

def revPosOfWF (s : String) (c : Char) : Option Pos :=
  revPosOfAuxWF s c s.endPos

def findAuxWF (s : String) (p : Char → Bool) (stopPos : Pos) (pos : Pos) : Pos :=
  if h : pos < stopPos then
    if p (s.get pos) then pos
    else
      have := Nat.sub_lt_sub_left h (lt_next s pos)
      findAuxWF s p stopPos (s.next pos)
  else pos
termination_by _ => stopPos.1 - pos.1

@[inline] def findWF (s : String) (p : Char → Bool) : Pos :=
  findAuxWF s p s.endPos 0

def revFindAuxWF (s : String) (p : Char → Bool) (pos : Pos) : Option Pos :=
  if h : pos = 0 then none
  else
    have := prev_lt_of_pos s pos h
    let pos := s.prev pos
    if p (s.get pos) then some pos
    else revFindAuxWF s p pos
termination_by _ => pos.1

def revFindWF (s : String) (p : Char → Bool) : Option Pos :=
  revFindAuxWF s p s.endPos

/-- Returns the first position where the two strings differ. -/
def firstDiffPosWF (a b : String) : Pos :=
  let stopPos := a.endPos.min b.endPos
  let rec loop (i : Pos) : Pos :=
    if h : i < stopPos then
      if a.get i != b.get i then i
      else
        have := Nat.sub_lt_sub_left h (lt_next a i)
        loop (a.next i)
    else i
  loop 0
termination_by loop => stopPos.1 - i.1

@[specialize] def splitAuxWF (s : String) (p : Char → Bool) (b : Pos) (i : Pos) (r : List String) : List String :=
  if h : s.atEnd i then
    let r := (s.extract b i)::r
    r.reverse
  else
    have := Nat.sub_lt_sub_left (Nat.gt_of_not_le (mt decide_eq_true h)) (lt_next s _)
    if p (s.get i) then
      let i' := s.next i
      splitAuxWF s p i' i' (s.extract b i :: r)
    else
      splitAuxWF s p b (s.next i) r
termination_by _ => s.endPos.1 - i.1

@[specialize] def splitWF (s : String) (p : Char → Bool) : List String :=
  splitAuxWF s p 0 0 []

def splitOnAuxWF (s sep : String) (b : Pos) (i : Pos) (j : Pos) (r : List String) : List String :=
  if h : s.atEnd i then
    let r := if sep.atEnd j then ""::(s.extract b (i - j))::r else (s.extract b i)::r
    r.reverse
  else
    have := Nat.sub_lt_sub_left (Nat.gt_of_not_le (mt decide_eq_true h)) (lt_next s _)
    if s.get i == sep.get j then
      let i := s.next i
      let j := sep.next j
      if sep.atEnd j then
        splitOnAuxWF s sep i i 0 (s.extract b (i - j)::r)
      else
        splitOnAuxWF s sep b i j r
    else
      splitOnAuxWF s sep b (s.next i) 0 r
termination_by _ => s.endPos.1 - i.1

def splitOnWF (s : String) (sep : String := " ") : List String :=
  if sep == "" then [s] else splitOnAuxWF s sep 0 0 0 []

def offsetOfPosAuxWF (s : String) (pos : Pos) (i : Pos) (offset : Nat) : Nat :=
  if i >= pos then offset
  else if h : s.atEnd i then
    offset
  else
    have := Nat.sub_lt_sub_left (Nat.gt_of_not_le (mt decide_eq_true h)) (lt_next s _)
    offsetOfPosAuxWF s pos (s.next i) (offset+1)
termination_by _ => s.endPos.1 - i.1

def offsetOfPosWF (s : String) (pos : Pos) : Nat :=
  offsetOfPosAuxWF s pos 0 0

@[specialize] def foldlAuxWF {α : Type u} (f : α → Char → α) (s : String) (stopPos : Pos) (i : Pos) (a : α) : α :=
  if h : i < stopPos then
    have := Nat.sub_lt_sub_left h (lt_next s i)
    foldlAuxWF f s stopPos (s.next i) (f a (s.get i))
  else a
termination_by _ => stopPos.1 - i.1

@[inline] def foldlWF {α : Type u} (f : α → Char → α) (init : α) (s : String) : α :=
  foldlAuxWF f s s.endPos 0 init

@[specialize] def foldrAuxWF {α : Type u} (f : Char → α → α) (a : α) (s : String) (i begPos : Pos) : α :=
  if h : begPos < i then
    have := String.prev_lt_of_pos s i <| mt (congrArg String.Pos.byteIdx) <|
      Ne.symm <| Nat.ne_of_lt <| Nat.lt_of_le_of_lt (Nat.zero_le _) h
    let i := s.prev i
    let a := f (s.get i) a
    foldrAuxWF f a s i begPos
  else a
termination_by _ => i.1

@[inline] def foldrWF {α : Type u} (f : Char → α → α) (init : α) (s : String) : α :=
  foldrAuxWF f init s s.endPos 0

@[specialize] def anyAuxWF (s : String) (stopPos : Pos) (p : Char → Bool) (i : Pos) : Bool :=
  if h : i < stopPos then
    if p (s.get i) then true
    else
      have := Nat.sub_lt_sub_left h (lt_next s i)
      anyAuxWF s stopPos p (s.next i)
  else false
termination_by _ => stopPos.1 - i.1

@[inline] def anyWF (s : String) (p : Char → Bool) : Bool :=
  anyAuxWF s s.endPos p 0

@[inline] def allWF (s : String) (p : Char → Bool) : Bool :=
  !s.anyWF (fun c => !p c)

def containsWF (s : String) (c : Char) : Bool :=
  s.anyWF (fun a => a == c)

theorem utf8SetAux_of_gt (c' : Char) : ∀ (cs : List Char) {i p : Pos}, i > p → utf8SetAux c' cs i p = cs
  | [],    _, _, _ => rfl
  | c::cs, i, p, h => by
    rw [utf8SetAux, if_neg (mt (congrArg (·.1)) (Ne.symm <| Nat.ne_of_lt h)), utf8SetAux_of_gt c' cs]
    exact Nat.lt_of_lt_of_le h (Nat.le_add_right ..)

theorem set_next_add (s : String) (i : Pos) (c : Char) (b₁ b₂)
    (h : (s.next i).1 + b₁ = s.endPos.1 + b₂) :
    ((s.set i c).next i).1 + b₁ = (s.set i c).endPos.1 + b₂ := by
  simp [next, get, set, endPos, utf8ByteSize] at h ⊢
  rw [Nat.add_comm i.1, Nat.add_assoc] at h ⊢
  let rec foo : ∀ cs a b₁ b₂,
    csize (utf8GetAux cs a i) + b₁ = utf8ByteSize.go cs + b₂ →
    csize (utf8GetAux (utf8SetAux c cs a i) a i) + b₁ = utf8ByteSize.go (utf8SetAux c cs a i) + b₂
  | [], _, _, _, h => h
  | c'::cs, a, b₁, b₂, h => by
    unfold utf8SetAux
    split <;> rename_i h' <;> simp [utf8GetAux, h', utf8ByteSize.go] at h ⊢
    next =>
      rw [Nat.add_assoc, Nat.add_left_comm] at h ⊢; rw [Nat.add_left_cancel h]
    next =>
      rw [Nat.add_assoc] at h ⊢
      refine foo cs (a + c') b₁ (csize c' + b₂) h
  exact foo s.1 0 _ _ h

theorem mapAux_lemma (s : String) (i : Pos) (c : Char) (h : ¬s.atEnd i) :
    (s.set i c).endPos.1 - ((s.set i c).next i).1 < s.endPos.1 - i.1 :=
  suffices (s.set i c).endPos.1 - ((s.set i c).next i).1 = s.endPos.1 - (s.next i).1 by
    rw [this]
    apply Nat.sub_lt_sub_left (Nat.gt_of_not_le (mt decide_eq_true h)) (lt_next ..)
  Nat.sub.elim (motive := (_ = ·)) _ _
    (fun _ k e =>
      have := set_next_add _ _ _ k 0 e.symm
      Nat.sub_eq_of_eq_add <| this.symm.trans <| Nat.add_comm ..)
    (fun h => by
      have ⟨k, e⟩ := Nat.le.dest h
      rw [Nat.succ_add] at e
      have : ((s.set i c).next i).1 = _ := set_next_add _ _ c 0 k.succ e.symm
      exact Nat.sub_eq_zero_of_le (this ▸ Nat.le_add_right ..))

@[specialize] def mapAuxWF (f : Char → Char) (i : Pos) (s : String) : String :=
  if h : s.atEnd i then s
  else
    let c := f (s.get i)
    have := mapAux_lemma s i c h
    let s := s.set i c
    mapAuxWF f (s.next i) s
termination_by _ => s.endPos.1 - i.1

@[inline] def mapWF (f : Char → Char) (s : String) : String :=
  mapAuxWF f 0 s

/--
Return `true` iff the substring of byte size `sz` starting at position `off1` in `s1` is equal to that starting at `off2` in `s2.`.
False if either substring of that byte size does not exist. -/
def substrEqWF (s1 : String) (off1 : String.Pos) (s2 : String) (off2 : String.Pos) (sz : Nat) : Bool :=
  off1.byteIdx + sz ≤ s1.endPos.byteIdx && off2.byteIdx + sz ≤ s2.endPos.byteIdx && loop off1 off2 { byteIdx := off1.byteIdx + sz }
where
  loop (off1 off2 stop1 : Pos) :=
    if h : off1.byteIdx < stop1.byteIdx then
      let c₁ := s1.get off1
      let c₂ := s2.get off2
      have := Nat.sub_lt_sub_left h (Nat.add_lt_add_left (one_le_csize c₁) off1.1)
      c₁ == c₂ && loop (off1 + c₁) (off2 + c₂) stop1
    else true
termination_by loop => stop1.1 - off1.1

/-- Return true iff `p` is a prefix of `s` -/
def isPrefixOfWF (p : String) (s : String) : Bool :=
  substrEqWF p 0 s 0 p.endPos.byteIdx

/-- Replace all occurrences of `pattern` in `s` with `replacement`. -/
def replaceWF (s pattern replacement : String) : String :=
  if h : pattern.endPos.1 = 0 then s
  else
    have hPatt := Nat.zero_lt_of_ne_zero h
    let rec loop (acc : String) (accStop pos : String.Pos) :=
      if h : pos.byteIdx + pattern.endPos.byteIdx > s.endPos.byteIdx then
        acc ++ s.extract accStop s.endPos
      else
        have := Nat.lt_of_lt_of_le (Nat.add_lt_add_left hPatt _) (Nat.ge_of_not_lt h)
        if s.substrEqWF pos pattern 0 pattern.endPos.byteIdx then
          have := Nat.sub_lt_sub_left this (Nat.add_lt_add_left hPatt _)
          loop (acc ++ s.extract accStop pos ++ replacement) (pos + pattern) (pos + pattern)
        else
          have := Nat.sub_lt_sub_left this (lt_next s pos)
          loop acc accStop (s.next pos)
    loop "" 0 0
termination_by loop => s.endPos.1 - pos.1

end String

namespace Substring

theorem lt_next (s : Substring) (i : String.Pos) (h : i.1 < s.bsize) :
    i.1 < (s.next i).1 := by
  simp [next]; rw [if_neg ?a]
  case a =>
    refine mt (congrArg String.Pos.byteIdx) (Nat.ne_of_lt ?_)
    exact (Nat.add_comm .. ▸ Nat.add_lt_of_lt_sub h :)
  apply Nat.lt_sub_of_add_lt
  rw [Nat.add_comm]; apply String.lt_next

def splitOnWF (s : Substring) (sep : String := " ") : List Substring :=
  if sep == "" then
    [s]
  else
    let rec loop (b i j : String.Pos) (r : List Substring) : List Substring :=
      if h : i.byteIdx < s.bsize then
        have := Nat.sub_lt_sub_left h (lt_next s i h)
        if s.get i == sep.get j then
          let i := s.next i
          let j := sep.next j
          if sep.atEnd j then
            loop i i 0 (s.extract b (i-j) :: r)
          else
            loop b i j r
        else
          loop b (s.next i) 0 r
      else
        let r := if sep.atEnd j then
          "".toSubstring :: s.extract b (i-j) :: r
        else
          s.extract b i :: r
        r.reverse
    loop 0 0 0 []
termination_by loop => s.bsize - i.1

@[inline] def foldlWF {α : Type u} (f : α → Char → α) (init : α) (s : Substring) : α :=
  match s with
  | ⟨s, b, e⟩ => String.foldlAuxWF f s e b init

@[inline] def foldrWF {α : Type u} (f : Char → α → α) (init : α) (s : Substring) : α :=
  match s with
  | ⟨s, b, e⟩ => String.foldrAuxWF f init s e b

@[inline] def anyWF (s : Substring) (p : Char → Bool) : Bool :=
  match s with
  | ⟨s, b, e⟩ => String.anyAuxWF s e p b

@[inline] def allWF (s : Substring) (p : Char → Bool) : Bool :=
  !s.anyWF (fun c => !p c)

def containsWF (s : Substring) (c : Char) : Bool :=
  s.anyWF (fun a => a == c)

@[specialize] def takeWhileAux (s : String) (stopPos : String.Pos) (p : Char → Bool) (i : String.Pos) : String.Pos :=
  if h : i < stopPos then
    if p (s.get i) then
      have := Nat.sub_lt_sub_left h (String.lt_next s i)
      takeWhileAux s stopPos p (s.next i)
    else i
  else i
termination_by _ => stopPos.1 - i.1

@[inline] def takeWhileWF : Substring → (Char → Bool) → Substring
  | ⟨s, b, e⟩, p =>
    let e := takeWhileAux s e p b;
    ⟨s, b, e⟩

@[inline] def dropWhileWF : Substring → (Char → Bool) → Substring
  | ⟨s, b, e⟩, p =>
    let b := takeWhileAux s e p b;
    ⟨s, b, e⟩

@[specialize] def takeRightWhileAux (s : String) (begPos : String.Pos) (p : Char → Bool) (i : String.Pos) : String.Pos :=
  if h : begPos < i then
    have := String.prev_lt_of_pos s i <| mt (congrArg String.Pos.byteIdx) <|
      Ne.symm <| Nat.ne_of_lt <| Nat.lt_of_le_of_lt (Nat.zero_le _) h
    let i' := s.prev i
    let c  := s.get i'
    if !p c then i
    else takeRightWhileAux s begPos p i'
  else i
termination_by _ => i.1

@[inline] def takeRightWhileWF : Substring → (Char → Bool) → Substring
  | ⟨s, b, e⟩, p =>
    let b := takeRightWhileAux s b p e
    ⟨s, b, e⟩

@[inline] def dropRightWhileWF : Substring → (Char → Bool) → Substring
  | ⟨s, b, e⟩, p =>
    let e := takeRightWhileAux s b p e
    ⟨s, b, e⟩

def beqWF (ss1 ss2 : Substring) : Bool :=
  ss1.bsize == ss2.bsize && ss1.str.substrEqWF ss1.startPos ss2.str ss2.startPos ss1.bsize

instance hasBeqWF : BEq Substring := ⟨beqWF⟩

end Substring

namespace String

def takeWhileWF (s : String) (p : Char → Bool) : String :=
  (s.toSubstring.takeWhileWF p).toString

def dropWhileWF (s : String) (p : Char → Bool) : String :=
  (s.toSubstring.dropWhileWF p).toString

def takeRightWhileWF (s : String) (p : Char → Bool) : String :=
  (s.toSubstring.takeRightWhileWF p).toString

def dropRightWhileWF (s : String) (p : Char → Bool) : String :=
  (s.toSubstring.dropRightWhileWF p).toString

@[inline] def nextWhileWF (s : String) (p : Char → Bool) (i : String.Pos) : String.Pos :=
  Substring.takeWhileAux s s.endPos p i

@[inline] def nextUntilWF (s : String) (p : Char → Bool) (i : String.Pos) : String.Pos :=
  nextWhileWF s (fun c => !p c) i

def toUpperWF (s : String) : String :=
  s.mapWF Char.toUpper

def toLowerWF (s : String) : String :=
  s.mapWF Char.toLower

end String
end deleteme

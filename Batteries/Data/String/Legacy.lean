/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura, Mario Carneiro
-/
module

/-!
# Legacy implementations of `String` operations

This file includes old definitions of `String` functions that were downstreamed from core to prevent
`Batteries.Data.String.Lemmas` from breaking.
-/

public section

namespace String

private noncomputable def utf8ByteSize' : String → Nat
  | s => go s.toList
where
  go : List Char → Nat
  | []    => 0
  | c::cs => go cs + c.utf8Size

private theorem utf8ByteSize'_eq (s : String) : s.utf8ByteSize' = s.utf8ByteSize := by
  suffices ∀ l, utf8ByteSize'.go l = (ofList l).utf8ByteSize by
    obtain ⟨m, rfl⟩ := s.exists_eq_ofList
    rw [utf8ByteSize', this, ofList_toList]
  intro l
  induction l with
  | nil => simp [utf8ByteSize'.go]
  | cons c cs ih =>
    rw [utf8ByteSize'.go, ih, ← List.singleton_append, String.ofList_append,
      utf8ByteSize_append, Nat.add_comm]
    congr
    rw [← size_bytes, String.bytes_ofList, List.utf8Encode_singleton,
      List.size_toByteArray, length_utf8EncodeChar]

private theorem set_next_add (s : String) (i : Pos.Raw) (c : Char) (b₁ b₂)
    (h : (i.next s).1 + b₁ = s.rawEndPos.1 + b₂) :
  (i.next (i.set s c)).1 + b₁ = (i.set s c).rawEndPos.1 + b₂ := by
  simp [Pos.Raw.next, Pos.Raw.get, Pos.Raw.set, rawEndPos, ← utf8ByteSize'_eq, utf8ByteSize'] at h ⊢
  rw [Nat.add_comm i.1, Nat.add_assoc] at h ⊢
  let rec foo : ∀ cs a b₁ b₂,
    (Pos.Raw.utf8GetAux cs a i).utf8Size + b₁ = utf8ByteSize'.go cs + b₂ →
    (Pos.Raw.utf8GetAux (Pos.Raw.utf8SetAux c cs a i) a i).utf8Size + b₁ =
      utf8ByteSize'.go (Pos.Raw.utf8SetAux c cs a i) + b₂
  | [], _, _, _, h => h
  | c'::cs, a, b₁, b₂, h => by
    unfold Pos.Raw.utf8SetAux
    apply iteInduction (motive := fun p =>
        (Pos.Raw.utf8GetAux p a i).utf8Size + b₁ = utf8ByteSize'.go p + b₂) <;>
      intro h' <;> simp [Pos.Raw.utf8GetAux, h', utf8ByteSize'.go] at h ⊢
    next =>
      rw [Nat.add_assoc, Nat.add_left_comm] at h ⊢; rw [Nat.add_left_cancel h]
    next =>
      rw [Nat.add_assoc] at h ⊢
      refine foo cs (a + c') b₁ (c'.utf8Size + b₂) h
  exact foo s.toList 0 _ _ h

private theorem mapAux_lemma (s : String) (i : Pos.Raw) (c : Char) (h : ¬i.atEnd s) :
    (i.set s c).rawEndPos.1 - (i.next (i.set s c)).1 < s.rawEndPos.1 - i.1 := by
  suffices (i.set s c).rawEndPos.1 - (i.next (i.set s c)).1 = s.rawEndPos.1 - (i.next s).1 by
    rw [this]
    apply Nat.sub_lt_sub_left (Nat.gt_of_not_le (mt decide_eq_true h)) (Pos.Raw.lt_next ..)
  have := set_next_add s i c (s.rawEndPos.byteIdx - (i.next s).byteIdx) 0
  have := set_next_add s i c 0 ((i.next s).byteIdx - s.rawEndPos.byteIdx)
  omega

/-- Implementation of `String.Legacy.map`. -/
@[specialize] def Legacy.mapAux (f : Char → Char) (i : Pos.Raw) (s : String) : String :=
  if h : i.atEnd s then s
  else
    let c := f (i.get s)
    have := mapAux_lemma s i c h
    let s := i.set s c
    mapAux f (i.next s) s
termination_by s.rawEndPos.1 - i.1

/--
Applies the function `f` to every character in a string, returning a string that contains the
resulting characters.

This is an old implementation, preserved here for users of the lemmas in
`Batteries.Data.String.Lemmas`. Its runtime behavior is equivalent to that of `String.map`.

Examples:
 * `"abc123".map Char.toUpper = "ABC123"`
 * `"".map Char.toUpper = ""`
-/
@[inline] def Legacy.map (f : Char → Char) (s : String) : String :=
  mapAux f 0 s

/--
Removes the specified number of characters (Unicode code points) from the start of the string.

If `n` is greater than `s.length`, returns `""`.

This is an old implementation, preserved here for users of the lemmas in
`Batteries.Data.String.Lemmas`. Its runtime behavior is equivalent to that of `String.drop`.

Examples:
 * `"red green blue".drop 4 = "green blue"`
 * `"red green blue".drop 10 = "blue"`
 * `"red green blue".drop 50 = ""`
-/
@[inline] def Legacy.drop (s : String) (n : Nat) : String :=
  (s.toRawSubstring.drop n).toString

/--
Creates a new string that contains the first `n` characters (Unicode code points) of `s`.

If `n` is greater than `s.length`, returns `s`.

This is an old implementation, preserved here for users of the lemmas in
`Batteries.Data.String.Lemmas`. Its runtime behavior is equivalent to that of `String.take`.

Examples:
* `"red green blue".take 3 = "red"`
* `"red green blue".take 1 = "r"`
* `"red green blue".take 0 = ""`
* `"red green blue".take 100 = "red green blue"`
-/
@[inline] def Legacy.take (s : String) (n : Nat) : String :=
  (s.toRawSubstring.take n).toString

/--
Creates a new string that contains the longest prefix of `s` in which `p` returns `true` for all
characters.

This is an old implementation, preserved here for users of the lemmas in
`Batteries.Data.String.Lemmas`. Its runtime behavior is equivalent to that of `String.takeWhile`.

Examples:
* `"red green blue".takeWhile (·.isLetter) = "red"`
* `"red green blue".takeWhile (· == 'r') = "r"`
* `"red green blue".takeWhile (· != 'n') = "red gree"`
* `"red green blue".takeWhile (fun _ => true) = "red green blue"`
-/
@[inline] def Legacy.takeWhile (s : String) (p : Char → Bool) : String :=
  (s.toRawSubstring.takeWhile p).toString

/--
Creates a new string by removing the longest prefix from `s` in which `p` returns `true` for all
characters.

This is an old implementation, preserved here for users of the lemmas in
`Batteries.Data.String.Lemmas`. Its runtime behavior is equivalent to that of `String.takeWhile`.

Examples:
* `"red green blue".dropWhile (·.isLetter) = " green blue"`
* `"red green blue".dropWhile (· == 'r') = "ed green blue"`
* `"red green blue".dropWhile (· != 'n') = "n blue"`
* `"red green blue".dropWhile (fun _ => true) = ""`
-/
@[inline] def Legacy.dropWhile (s : String) (p : Char → Bool) : String :=
  (s.toRawSubstring.dropWhile p).toString

/--
Auxuliary definition for `String.Legacy.posOf`.

This is an old implementation, preserved here for users of the lemmas in
`Batteries.Data.String.Lemmas`.
-/
def Legacy.posOfAux (s : String) (c : Char) (stopPos : Pos.Raw) (pos : Pos.Raw) : Pos.Raw :=
  if h : pos < stopPos then
    if pos.get s == c then pos
    else
      have := Nat.sub_lt_sub_left h (Pos.Raw.lt_next s pos)
      posOfAux s c stopPos (pos.next s)
  else pos
termination_by stopPos.1 - pos.1

/--
Returns the position of the first occurrence of a character, `c`, in a string `s`. If `s` does not
contain `c`, returns `s.rawEndPos`.

This is an old implementation, preserved here for users of the lemmas in
`Batteries.Data.String.Lemmas`.

Examples:
* `"abcba".posOf 'a' = ⟨0⟩`
* `"abcba".posOf 'z' = ⟨5⟩`
* `"L∃∀N".posOf '∀' = ⟨4⟩`
-/
@[inline] def Legacy.posOf (s : String) (c : Char) : Pos.Raw :=
  posOfAux s c s.rawEndPos 0

/--
Auxuliary definition for `String.Legacy.revPosOf`.

This is an old implementation, preserved here for users of the lemmas in
`Batteries.Data.String.Lemmas`.
-/
def Legacy.revPosOfAux (s : String) (c : Char) (pos : Pos.Raw) : Option Pos.Raw :=
  if h : pos = 0 then none
  else
    have := Pos.Raw.prev_lt_of_pos s pos h
    let pos := pos.prev s
    if pos.get s == c then some pos
    else revPosOfAux s c pos
termination_by pos.1

/--
Returns the position of the last occurrence of a character, `c`, in a string `s`. If `s` does not
contain `c`, returns `none`.

This is an old implementation, preserved here for users of the lemmas in
`Batteries.Data.String.Lemmas`.

Examples:
* `"abcabc".revPosOf 'a' = some ⟨3⟩`
* `"abcabc".revPosOf 'z' = none`
* `"L∃∀N".revPosOf '∀' = some ⟨4⟩`
-/
@[inline] def Legacy.revPosOf (s : String) (c : Char) : Option Pos.Raw :=
  revPosOfAux s c s.rawEndPos

/--
Auxuliary definition for `String.Legacy.find`.

This is an old implementation, preserved here for users of the lemmas in
`Batteries.Data.String.Lemmas`.
-/
def Legacy.findAux (s : String) (p : Char → Bool) (stopPos : Pos.Raw) (pos : Pos.Raw) : Pos.Raw :=
  if h : pos < stopPos then
    if p (pos.get s) then pos
    else
      have := Nat.sub_lt_sub_left h (Pos.Raw.lt_next s pos)
      findAux s p stopPos (pos.next s)
  else pos
termination_by stopPos.1 - pos.1

/--
Finds the position of the first character in a string for which the Boolean predicate `p` returns
`true`. If there is no such character in the string, then the end position of the string is
returned.

This is an old implementation, preserved here for users of the lemmas in
`Batteries.Data.String.Lemmas`.

Examples:
 * `"coffee tea water".find (·.isWhitespace) = ⟨6⟩`
 * `"tea".find (· == 'X') = ⟨3⟩`
 * `"".find (· == 'X') = ⟨0⟩`
-/
@[inline] def Legacy.find (s : String) (p : Char → Bool) : Pos.Raw :=
  findAux s p s.rawEndPos 0

/--
Auxuliary definition for `String.Legacy.revFind`.

This is an old implementation, preserved here for users of the lemmas in
`Batteries.Data.String.Lemmas`.
-/
def Legacy.revFindAux (s : String) (p : Char → Bool) (pos : Pos.Raw) : Option Pos.Raw :=
  if h : pos = 0 then none
  else
    have := Pos.Raw.prev_lt_of_pos s pos h
    let pos := pos.prev s
    if p (pos.get s) then some pos
    else revFindAux s p pos
termination_by pos.1

/--
Finds the position of the last character in a string for which the Boolean predicate `p` returns
`true`. If there is no such character in the string, then `none` is returned.

This is an old implementation, preserved here for users of the lemmas in
`Batteries.Data.String.Lemmas`.

Examples:
 * `"coffee tea water".revFind (·.isWhitespace) = some ⟨10⟩`
 * `"tea".revFind (· == 'X') = none`
 * `"".revFind (· == 'X') = none`
-/
@[inline] def Legacy.revFind (s : String) (p : Char → Bool) : Option Pos.Raw :=
  revFindAux s p s.rawEndPos

end String

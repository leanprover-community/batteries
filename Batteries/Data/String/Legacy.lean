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
  | s => go s.data
where
  go : List Char → Nat
  | []    => 0
  | c::cs => go cs + c.utf8Size

private theorem utf8ByteSize'_eq (s : String) : s.utf8ByteSize' = s.utf8ByteSize := by
  suffices ∀ l, utf8ByteSize'.go l = l.asString.utf8ByteSize by
    obtain ⟨m, rfl⟩ := s.exists_eq_asString
    rw [utf8ByteSize', this, asString_data]
  intro l
  induction l with
  | nil => simp [utf8ByteSize'.go]
  | cons c cs ih =>
    rw [utf8ByteSize'.go, ih, ← List.singleton_append, List.asString_append,
      utf8ByteSize_append, Nat.add_comm]
    congr
    rw [← size_bytes, List.bytes_asString, List.utf8Encode_singleton,
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
  exact foo s.data 0 _ _ h

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

end String

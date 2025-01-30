/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg, James Gallicchio, F. G. Dorais
-/

instance : Coe String Substring := ⟨String.toSubstring⟩

namespace String

/-- Count the occurrences of a character in a string. -/
def count (s : String) (c : Char) : Nat :=
  s.foldl (fun n d => if d = c then n + 1 else n) 0

/--
Convert a string of assumed-ASCII characters into a byte array.
(If any characters are non-ASCII they will be reduced modulo 256.)

Note: if you just need the underlying `ByteArray` of a non-ASCII string,
use `String.toUTF8`.
-/
def toAsciiByteArray (s : String) : ByteArray :=
  let rec
  /--
  Internal implementation of `toAsciiByteArray`.
  `loop p out = out ++ toAsciiByteArray ({ s with startPos := p } : Substring)`
  -/
  loop (p : Pos) (out : ByteArray) : ByteArray :=
    if h : s.atEnd p then out else
    let c := s.get p
    have : utf8ByteSize s - (next s p).byteIdx < utf8ByteSize s - p.byteIdx :=
      Nat.sub_lt_sub_left (Nat.lt_of_not_le <| mt decide_eq_true h)
        (Nat.lt_add_of_pos_right (Char.utf8Size_pos _))
    loop (s.next p) (out.push c.toUInt8)
    termination_by utf8ByteSize s - p.byteIdx
  loop 0 ByteArray.empty

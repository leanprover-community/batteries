/-
Copyright (c) 2024 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: François G. Dorais
-/
import Batteries.Data.Array.Match
import Batteries.Data.String.Basic

namespace List

/-- Knuth-Morris-Pratt matcher type

This type is used to keep data for running the Knuth-Morris-Pratt (KMP) list matching algorithm.
KMP is a linear time algorithm to locate all contiguous sublists of a list that match a given
pattern. Generating the algorithm data is also linear in the length of the pattern but the data can
be re-used to match the same pattern over multiple lists.

The KMP data for a pattern can be generated using `Matcher.ofList`. Then `Matcher.find?` and
`Matcher.findAll` can be used to run the algorithm on an input list.
```
def m := Matcher.ofList [0,1,1,0]

#eval Option.isSome <| m.find? [2,1,1,0,1,1,2] -- false
#eval Option.isSome <| m.find? [0,0,1,1,0,0] -- true

#eval Array.size <| m.findAll [0,1,1,0,1,1,0] -- 2
#eval Array.size <| m.findAll [0,1,1,0,1,1,0,1,1,0] -- 3
```
-/
structure Matcher (α : Type _) extends Array.Matcher α where
  /-- The pattern for the matcher -/
  pattern : List α

/-- Make KMP matcher from list pattern. -/
@[inline] def Matcher.ofList [BEq α] (pattern : List α) : Matcher α where
  toMatcher := Array.Matcher.ofStream pattern
  pattern := pattern

/-- List stream that keeps count of items read. -/
local instance (α) : Stream (List α × Nat) α where
  next?
  | ([], _) => none
  | (x::xs, n) => (x, xs, n+1)

/--
Find all start and end positions of all infix sublists of `l` matching `m.pattern`.
The sublists may be overlapping.
-/
partial def Matcher.findAll [BEq α] (m : Matcher α) (l : List α) : Array (Nat × Nat) :=
  loop (l, 0) m.toMatcher #[]
where
  /-- Accumulator loop for `List.Matcher.findAll` -/
  loop (l : List α × Nat) (am : Array.Matcher α) (occs : Array (Nat × Nat)) : Array (Nat × Nat) :=
    match am.next? l with
    | none => occs
    | some (l, am) => loop l am (occs.push (l.snd - m.table.size, l.snd))

/--
Find the start and end positions of the first infix sublist of `l` matching `m.pattern`,
or `none` if there is no such sublist.
-/
def Matcher.find? [BEq α] (m : Matcher α) (l : List α) : Option (Nat × Nat) :=
  match m.next? (l, 0) with
  | none => none
  | some (l, _) => some (l.snd - m.table.size, l.snd)

/--
Returns all the start and end positions of all infix sublists of of `l` that match `pattern`.
The sublists may be overlapping.
-/
@[inline] def findAllInfix [BEq α] (l pattern : List α) : Array (Nat × Nat) :=
  (Matcher.ofList pattern).findAll l

/--
Returns the start and end positions of the first infix sublist of `l` that matches `pattern`,
or `none` if there is no such sublist.
-/
@[inline] def findInfix? [BEq α] (l pattern : List α) : Option (Nat × Nat) :=
  (Matcher.ofList pattern).find? l

/--
Returns true iff `pattern` occurs as an infix sublist of `l`.
-/
@[inline] def containsInfix [BEq α] (l pattern : List α) : Bool :=
  findInfix? l pattern |>.isSome

import Batteries.Data.Array.Match
import Std.Data.Iterators

open Std Std.Iterators

def matchSuffixes (pattern input : List Nat) : List (List Nat) := Id.run do
  let m := Array.Matcher.ofArray pattern.toArray
  let it : IterM (α := m.Iterator _ Id Nat) Id _ :=
    ⟨{ inner := input.iter.toIterM }⟩
  return it.toList.map (·.list)

#guard matchSuffixes [1, 2] [0, 1, 2, 3] == [[3]]
#guard matchSuffixes [1, 1] [1, 1, 1] == [[1], []]
#guard matchSuffixes [1, 2, 1] [1, 2, 2, 1, 2, 1] == [[]]
#guard matchSuffixes [1, 2] [1, 3, 2] == []

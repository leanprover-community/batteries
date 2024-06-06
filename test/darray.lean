import Batteries.Data.DArray.Basic

open Batteries

def foo : DArray 3 fun | 0 => String | 1 => Nat | 2 => Array Nat :=
  .mk fun | 0 => "foo" | 1 => 42 | 2 => #[4, 2]

def bar := foo.set 0 "bar"

#guard foo.get 0 == "foo"
#guard foo.get 1 == 42
#guard foo.get 2 == #[4, 2]

#guard (foo.set 1 1).get 0 == "foo"
#guard (foo.set 1 1).get 1 == 1
#guard (foo.set 1 1).get 2 == #[4, 2]

#guard bar.get 0 == "bar"
#guard (bar.set 0 (foo.get 0)).get 0 == "foo"
#guard ((bar.set 0 "baz").set 1 1).get 0 == "baz"
#guard ((bar.set 0 "baz").set 0 "foo").get 0 == "foo"
#guard ((bar.set 0 "foo").set 0 "baz").get 0 == "baz"

def Batteries.DArray.head : DArray (n+1) α → α 0
  | mk f => f 0

#guard foo.head == "foo"
#guard bar.head == "bar"

abbrev Data (n : Nat) : Type _ := DArray (n+1) fun | 0 => String | ⟨_+1,_⟩ => Nat

def Data.sum (a : Data n) : String × Nat := Id.run do
  let mut r := ("", 0)
  for ⟨i, x⟩ in a do
    match i with
    | 0 => r := (x, r.snd)
    | ⟨_+1,_⟩ => r := ⟨r.fst, r.snd+x⟩
  return r

def test : Data 2 :=
  .mk fun | 0 => "foo" | 1 => 4 | 2 => 2

#guard test.sum == ("foo", 6)

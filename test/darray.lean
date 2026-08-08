import Batteries.Data.DArray

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

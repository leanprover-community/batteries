import Batteries.Data.DArray

open Batteries

def foo : DArray 3 fun | 0 => String | 1 => Nat | 2 => Array Nat :=
  .mk fun | 0 => "foo" | 1 => 42 | 2 => #[4, 2]

#guard foo.get 0 == "foo"
#guard foo.get 1 == 42
#guard foo.get 2 == #[4, 2]

#guard (foo.set 1 1).get 0 == "foo"
#guard (foo.set 1 1).get 1 == 1
#guard (foo.set 1 1).get 2 == #[4, 2]

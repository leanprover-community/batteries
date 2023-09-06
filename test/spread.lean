import Std.Tactic.Spread
import Std.Tactic.GuardMsgs

set_option linter.missingDocs false

class One (α : Type) where
  bar : Nat

class Two (α : Type) where
  bar : Nat
  qux : Nat

class Bar where
  bar : Nat

class Qux where
  qux : Nat

class Both where
  bar : Nat
  qux : Nat

instance : Bar where
  bar := 0

instance : Qux where
  qux := 0

instance : Both where
  bar := 1
  qux := 1

instance : One α where
  __ := instBar -- include fields from `instBar`

example : One α := {
  __ := instBar -- include fields from `instBar`
}

instance : Two α where
  __ := instBar
  __ := instQux

instance : Two α where
  __ := instBoth

/-- error: fields missing: 'qux' -/
#guard_msgs in
instance : Two α where
  __ := instBar

instance : Two α where
  qux := 0
  __ := instBar

instance : Two α where
  __ := instBar
  qux := 0

-- An explicit field has priority over the spread.
def a : Two α where
  __ := instBoth
  qux := 0

example : @Two.bar α a = 1 := rfl
example : @Two.qux α a = 0 := rfl

-- An explicit field has priority over the spread, regardless of the order.
def b : Two α where
  qux := 0
  __ := instBoth

example : @Two.bar α b = 1 := rfl
example : @Two.qux α b = 0 := rfl

-- With multiple spreads, earlier ones take priority.
def c : Two α where
  __ := instQux
  __ := instBoth

example : @Two.bar α c = 1 := rfl
example : @Two.qux α c = 0 := rfl

-- With multiple spreads, earlier ones take priority.
def d : Two α where
  __ := instBoth
  __ := instQux

example : @Two.bar α d = 1 := rfl
example : @Two.qux α d = 1 := rfl

import Std.Tactic.PrintInstances

class Foo (α : Type) : Type

instance fooNat1 : Foo Nat := {}
instance fooNat2 : Foo Nat := {}
instance (priority := low) fooProd [Foo α] : Foo (α × α) := {}

variable [localVar : Foo α]

/--
info: localVar : Foo α
fooNat2 : Foo Nat
fooNat1 : Foo Nat
fooProd {α : Type} [inst✝ : Foo α] : Foo (α × α)
-/
#guard_msgs in #print instances Foo

import Std.Tactic.Lint.TypeClass
open Std.Tactic.Lint

namespace A
local instance impossible {α β : Type} [Inhabited α] : Nonempty α := ⟨default⟩
#eval do guard (← impossibleInstance.test ``impossible).isSome
end A

namespace B
class VectorSpace (K : outParam Type) (V : Type) extends Add V
#eval do guard (← dangerousInstance.test ``VectorSpace.toAdd).isNone
end B

namespace C
class VectorSpace (K : Type) (V : Type) extends Add V
#eval do guard (← dangerousInstance.test ``VectorSpace.toAdd).isSome
end C

namespace D
class OrderHomClass (F : Type) (α β : outParam Type) [LE α] [LE β]
instance dangerous [LE α] [LE β] [OrderHomClass F α β] : CoeFun F fun _ => α → β := sorry
#eval do guard (← dangerousInstance.test ``dangerous).isSome
instance fixed {_ : LE α} {_ : LE β} [OrderHomClass F α β] : CoeFun F fun _ => α → β := sorry
#eval do guard (← dangerousInstance.test ``fixed).isNone
end D

namespace E
class Foo (α : Type)
class Bar (α : Type) [LE α] extends Foo α
#eval do guard (← dangerousInstance.test ``Bar.toFoo).isNone
end E

namespace F
class Foo (α : outParam Type)
abbrev Foo' := Foo
instance dangerous [Inhabited α] : Foo' α where
#eval do guard (← dangerousInstance.test ``dangerous).isSome
end F

import Std.Tactic.Lint.TypeClass
open Std.Tactic.Lint

namespace A
local instance impossible {α β : Type} [Inhabited α] : Nonempty α := ⟨default⟩
#eval do guard (← impossibleInstance.test ``impossible).isSome
end A

namespace B
instance bad : Nat := 1
#eval do guard (← nonClassInstance.test ``bad).isSome
instance good : Inhabited Nat := ⟨1⟩
#eval do guard (← nonClassInstance.test ``good).isNone
end B

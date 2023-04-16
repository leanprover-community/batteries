import Std.Tactic.Lint.TypeClass
open Std.Tactic.Lint

namespace A
local instance impossible {α β : Type} [Inhabited α] : Nonempty α := ⟨default⟩
#eval do guard (← impossibleInstance.test ``impossible).isSome
end A

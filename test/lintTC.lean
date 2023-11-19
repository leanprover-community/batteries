import Std.Tactic.Lint.TypeClass
import Std.Tactic.GuardMsgs

open Std.Tactic.Lint

namespace A

/-- warning: unused variable `β` [linter.unusedVariables] -/
#guard_msgs in
local instance impossible {α β : Type} [Inhabited α] : Nonempty α := ⟨default⟩

#eval do guard (← impossibleInstance.test ``impossible).isSome

end A

namespace B
instance bad : Nat := 1

#eval do guard (← nonClassInstance.test ``bad).isSome
instance good : Inhabited Nat := ⟨1⟩

#eval do guard (← nonClassInstance.test ``good).isNone
end B

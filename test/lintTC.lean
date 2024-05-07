import Batteries.Tactic.Lint.TypeClass
import Lean.Elab.Command

open Std.Tactic.Lint

namespace A

/--
warning: unused variable `β`
note: this linter can be disabled with `set_option linter.unusedVariables false`
-/
#guard_msgs in
local instance impossible {α β : Type} [Inhabited α] : Nonempty α := ⟨default⟩

run_meta guard (← impossibleInstance.test ``impossible).isSome

end A

namespace B
instance bad : Nat := 1

run_meta guard (← nonClassInstance.test ``bad).isSome
instance good : Inhabited Nat := ⟨1⟩

run_meta guard (← nonClassInstance.test ``good).isNone
end B

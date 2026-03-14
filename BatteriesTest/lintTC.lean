import Batteries.Tactic.Lint.TypeClass
import Lean.Elab.Command

open Batteries.Tactic.Lint

namespace A

/--
warning: unused variable `β`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
---
warning: This instance has at least one argument that is impossible to infer for typeclass inference. Specifically
    argument 2: `{β : Type}`
These are arguments that are not instance-implicit and appear neither in another instance-implicit argument nor the return type, so they can't be filled in by typeclass inference.

Note: This linter can be disabled with `set_option linter.impossibleInstance' false`
-/
#guard_msgs in
local instance impossible {α β : Type} [Inhabited α] : Nonempty α := ⟨default⟩

run_meta guard (← impossibleInstance.test ``impossible).isSome

end A

namespace B

/--
warning: This declaration should not be an instance as it is not class-valued.

Note: This linter can be disabled with `set_option linter.nonClassInstance' false`
-/
#guard_msgs in
instance bad : Nat := 1

run_meta guard (← nonClassInstance.test ``bad).isSome
instance good : Inhabited Nat := ⟨1⟩

run_meta guard (← nonClassInstance.test ``good).isNone
end B

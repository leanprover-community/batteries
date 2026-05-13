import Batteries.Tactic.Lint.TypeClass
import Lean.Elab.Command

open Batteries.Tactic.Lint

namespace A

/--
error: Instance @impossible has arguments β : Type that are impossible to infer. Those arguments are not instance-implicit and do not appear in another instance-implicit argument or the return type.
-/
#guard_msgs in
local instance impossible {α β : Type} [Inhabited α] : Nonempty α := ⟨default⟩

end A

namespace B
/-- error: instance `B.bad` target `Nat` is not a type class. -/
#guard_msgs in
instance bad : Nat := 1

instance good : Inhabited Nat := ⟨1⟩

end B

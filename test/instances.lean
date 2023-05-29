import Std.Tactic.Instances
import Std.Tactic.GuardMsgs

/--
error: type class instance expected
  Fin 1
-/
#guard_msgs in
#instances Fin 1

/--
info: 1 instance:

instAddNat : Add Nat
-/
#guard_msgs in
#instances Add Nat

namespace Testing
class A (α : Type)

/-- info: No instances -/
#guard_msgs in
#instances A

instance : A Nat := ⟨⟩
instance : A Bool := ⟨⟩

/--
info: 2 instances:

instANat : A Nat
instABool : A Bool
-/
#guard_msgs in
#instances A _

/--
info: 2 instances:

instANat : A Nat
instABool : A Bool
-/
#guard_msgs in
#instances A

/-- info: No instances -/
#guard_msgs in
#instances (α : Type) → A α

instance : A α := ⟨⟩

/--
info: 1 instance:

@instA : {α : Type} → A α
-/
#guard_msgs in
#instances (α : Type) → A α

end Testing

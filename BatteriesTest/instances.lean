import Batteries.Tactic.Instances

set_option linter.missingDocs false

/--
error: type class instance expected
  Fin 1
-/
#guard_msgs in
#instances Fin 1

/--
info: 4 instances:

instAddNat : Add Nat
(prio 100) Lean.Grind.IntModule.toAdd.{u} {M : Type u} [self : Lean.Grind.IntModule M] : Add M
(prio 100) Lean.Grind.NatModule.toAdd.{u} {M : Type u} [self : Lean.Grind.NatModule M] : Add M
(prio 100) Lean.Grind.Semiring.toAdd.{u} {α : Type u} [self : Lean.Grind.Semiring α] : Add α
-/
#guard_msgs in
#instances Add Nat

namespace Testing
class A (α : Type)

/-- info: No instances -/
#guard_msgs in
#instances A

instance (priority := high) : A Nat := ⟨⟩
instance : A Int := ⟨⟩
instance : A Bool := ⟨⟩

/--
info: 3 instances:

(prio 10000) Testing.instANat : A Nat
Testing.instABool : A Bool
Testing.instAInt : A Int
-/
#guard_msgs in
#instances A _

/--
info: 3 instances:

(prio 10000) Testing.instANat : A Nat
Testing.instABool : A Bool
Testing.instAInt : A Int
-/
#guard_msgs in
#instances A

/-- info: No instances -/
#guard_msgs in
#instances (α : Type) → A α

instance : A α := ⟨⟩

/--
info: 5 instances:
(local) inst✝ : A β
(prio 10000) Testing.instANat : A Nat
Testing.instABool : A Bool
Testing.instAInt : A Int
Testing.instA {α : Type} : A α
-/
#guard_msgs in
#instances [A β] : A

/--
info: 1 instance:

Testing.instA {α : Type} : A α
-/
#guard_msgs in
#instances (α : Type) → A α

end Testing

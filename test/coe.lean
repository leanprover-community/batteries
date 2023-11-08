import Std.Tactic.CoeExt
import Std.Tactic.GuardMsgs

set_option linter.missingDocs false

structure WrappedNat where
  val : Nat


structure WrappedFun where
  fn : Nat → Nat


structure WrappedType where
  typ : Type

attribute [coe] WrappedNat.val
#eval Std.Tactic.Coe.registerCoercion ``WrappedFun.fn (some ⟨1, 0, .coeFun⟩)
#eval Std.Tactic.Coe.registerCoercion ``WrappedType.typ (some ⟨1, 0, .coeSort⟩)


variable (n : WrappedNat) (f : WrappedFun) (t : WrappedType)

/-- info: ↑n : Nat -/
#guard_msgs in #check n.val

/-- info: ⇑f : Nat → Nat-/
#guard_msgs in #check f.fn

/-- info: ↥t : Type -/
#guard_msgs in #check t.typ

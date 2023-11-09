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
instance : Coe WrappedNat Nat where coe := WrappedNat.val

#eval Std.Tactic.Coe.registerCoercion ``WrappedFun.fn (some ⟨1, 0, .coeFun⟩)
instance : CoeFun WrappedFun (fun _ => Nat → Nat) where coe := WrappedFun.fn

#eval Std.Tactic.Coe.registerCoercion ``WrappedType.typ (some ⟨1, 0, .coeSort⟩)
instance : CoeSort WrappedType Type where coe := WrappedType.typ


variable (n : WrappedNat) (f : WrappedFun) (t : WrappedType)

/-- info: ↑n : Nat -/
#guard_msgs in #check n.val
/-- info: ↑n : Nat -/
#guard_msgs in #check (↑n : Nat)

/-- info: ⇑f : Nat → Nat-/
#guard_msgs in #check f.fn
/-- info: ⇑f : Nat → Nat-/
#guard_msgs in #check ⇑f
/-- info: ⇑f 1 : Nat-/
#guard_msgs in #check ⇑f 1

/-- info: ↥t : Type -/
#guard_msgs in #check t.typ
/-- info: ↥t : Type -/
#guard_msgs in #check ↥t

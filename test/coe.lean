import Std.Tactic.GuardMsgs

set_option linter.missingDocs false

structure WrappedNat where
  val : Nat


structure WrappedFun (α) where
  fn : Nat → α


structure WrappedType where
  typ : Type

attribute [coe] WrappedNat.val
instance : Coe WrappedNat Nat where coe := WrappedNat.val

#eval Lean.Meta.registerCoercion ``WrappedFun.fn (some ⟨2, 1, .coeFun⟩)
instance : CoeFun (WrappedFun α) (fun _ => Nat → α) where coe := WrappedFun.fn

#eval Lean.Meta.registerCoercion ``WrappedType.typ (some ⟨1, 0, .coeSort⟩)
instance : CoeSort WrappedType Type where coe := WrappedType.typ

section coe
variable (n : WrappedNat)

/-- info: ↑n : Nat -/
#guard_msgs in #check n.val
/-- info: ↑n : Nat -/
#guard_msgs in #check (↑n : Nat)

end coe

section coeFun
variable (f : WrappedFun Nat) (g : Nat → WrappedFun Nat) (h : WrappedFun (WrappedFun Nat))

/-- info: ⇑f : Nat → Nat -/
#guard_msgs in #check f.fn
/-- info: ⇑f : Nat → Nat -/
#guard_msgs in #check ⇑f
-- applied functions do not need the `⇑`
/-- info: f 1 : Nat -/
#guard_msgs in #check ⇑f 1

/-- info: ⇑(g 1) : Nat → Nat -/
#guard_msgs in #check ⇑(g 1)
/-- info: (g 1) 2 : Nat -/  -- TODO: remove the `()`?
#guard_msgs in #check g 1 2

/-- info: ⇑h : Nat → WrappedFun Nat -/
#guard_msgs in #check ⇑h
/-- info: h 1 : WrappedFun Nat -/
#guard_msgs in #check h 1
/-- info: ⇑(h 1) : Nat → Nat -/
#guard_msgs in #check ⇑(h 1)
/-- info: (h 1) 2 : Nat -/  -- TODO: remove the `()`?
#guard_msgs in #check h 1 2

end coeFun

section coeSort
variable (t : WrappedType)

/-- info: ↥t : Type -/
#guard_msgs in #check t.typ
/-- info: ↥t : Type -/
#guard_msgs in #check ↥t

end coeSort

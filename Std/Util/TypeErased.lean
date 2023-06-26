/-
Copyright (c) 2023 James Gallicchio.

Authors: James Gallicchio
-/

namespace Std.TypeErased

private structure Intf.{u} where
  TypeErased : Type u
  type : TypeErased → Type u
  proj (t : TypeErased) : type t
  inj : α → TypeErased
  type_inj (a : α) : type (inj a) = α
  proj_inj (a : α) : proj (inj a) = cast (type_inj a).symm a

/-- States that `Intf.TypeErased` is a safe interface. -/
axiom InftSafe.{u} : Nonempty (TypeErased.Intf.{u})

attribute [instance] InftSafe in
private noncomputable opaque Impl.{u} : TypeErased.Intf.{u}

end TypeErased

/-- A value of some noncomputable type. -/
def TypeErased.{u} : Type u := TypeErased.Impl.TypeErased

namespace TypeErased

/-- The type of `v`. -/
noncomputable def type : (v : TypeErased) → Type u := Impl.type

/- Actual implementation of the computable portion of the interface. -/
private unsafe def getUnsafe (v : TypeErased.{u}) : v.type := unsafeCast v
private unsafe def mkUnsafe {α : Type u} (a : α) : TypeErased.{u} := unsafeCast a

/-- Project `v` to the underlying value, of type `v.type`. -/
@[implemented_by getUnsafe] def get (v : TypeErased.{u}) : v.type := Impl.proj v
/-- Erase the type of `a`. -/
@[implemented_by mkUnsafe] def mk (a : α) : TypeErased := Impl.inj a

/-- Project `v` to the underlying value of type `α`. -/
protected def cast (v : TypeErased) (h : v.type = α) : α :=
  cast h v.get

instance : Inhabited TypeErased := ⟨mk ()⟩

@[simp] theorem type_mk (a : α) : (mk a).type = α := Impl.type_inj _
theorem get_mk {a : α} : (mk a).get = cast (type_mk a).symm a := Impl.proj_inj _
@[simp] theorem cast_mk (a : α) (h : (mk a).type = β) : (mk a).cast h = cast (Eq.trans (type_mk a).symm h) a := by
  unfold TypeErased.cast; rw [get_mk]
  cases h
  congr

@[simp] theorem cast_cast (v : TypeErased) (h : v.type = α) (h' : α = β) : cast h' (v.cast h) = v.cast (h.trans h') := by
  cases h'; cases h
  simp [TypeErased.cast, cast]

theorem cast_rw {v v' : TypeErased} (h : v.type = α) (h' : v = v') : v.cast h = v'.cast (h' ▸ h) := by
  cases h'; cases h; simp

/-
Copyright (c) 2024 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: François G. Dorais
-/

namespace Batteries

/-- `DArray` is a heterogenous array with element types given by `type`. -/
inductive DArray (n) (α : Fin n → Type _) where
/-- `DArray` constructor. -/
| mk (get : (i : Fin n) → α i)

namespace DArray

  /-- Gets the `DArray` item at index `i`. -/
protected def get : DArray n α → (i : Fin n) → α i
  | mk get => get

/-- Sets the `DArray` item at index `i`. -/
protected def set (a : DArray n α) (i : Fin n) (v : α i) : DArray n α :=
  mk fun j => if h : i = j then h ▸ v else a.get j

@[ext]
protected theorem ext : {a b : DArray n α} → (∀ i, a.get i = b.get i) → a = b
  | mk _, mk _, h => congrArg _ <| funext fun i => h i

@[simp]
theorem get_set (a : DArray n α) (i : Fin n) (v : α i) : (a.set i v).get i = v := by
  simp only [DArray.get, DArray.set, dif_pos]

theorem get_set_ne (a : DArray n α) (v : α i) (h : i ≠ j) : (a.set i v).get j = a.get j := by
  simp only [DArray.get, DArray.set, dif_neg h]

@[simp]
theorem set_set {type : Fin size → Type _} (a : DArray size type) (i : Fin size)
    (v w : type i) : (a.set i v).set i w = a.set i w := by
  ext j
  if h : i = j then
    rw [← h, get_set, get_set]
  else
    rw [get_set_ne _ _ h, get_set_ne _ _ h, get_set_ne _ _ h]

@[simp]
theorem get_mk (i : Fin size) : DArray.get (.mk init) i = init i := by
  simp [DArray.get, DArray.mk]

theorem set_mk {type : Fin size → Type _} {init} (i : Fin size) (v : type i) :
    DArray.set (.mk init) i v = .mk fun j => if h : i = j then h ▸ v else init j := by
  ext j
  if h : i = j then
    rw [← h, get_set, get_mk, dif_pos rfl]
  else
    rw [get_set_ne _ _ h, get_mk, get_mk, dif_neg h]

/-! # Experimental Unsafe Implementation

For this implementation, `DArray n α` is secretly stored as an `Array Unit` with size `n`. This
works because Lean never actually checks that the objects stored in an array have the appropriate
type. So it's safe, in principle, to `unsafeCast` the fake `Unit` objects to the appropriate type
and similarly to `unsafeCast` any relevant object to a fake `Unit` object.
-/

private unsafe def mkUnsafe (get : (i : Fin size) → type i) : DArray size type :=
  let data : Array Unit := .ofFn fun i => unsafeCast (get i)
  unsafeCast data

private unsafe def getUnsafe (a : DArray size type) (i) : type i :=
  let data : Array Unit := unsafeCast a
  unsafeCast <| data[i.val]'(lcProof)

private unsafe def setUnsafe (a : DArray size type) (i) (v : type i) : DArray size type :=
  let data : Array Unit := unsafeCast a
  unsafeCast <| data.set ⟨i.val, lcProof⟩ <| unsafeCast v

attribute [implemented_by mkUnsafe] DArray.mk
attribute [implemented_by getUnsafe] DArray.get
attribute [implemented_by setUnsafe] DArray.set

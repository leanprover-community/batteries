/-
Copyright (c) 2024 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: François G. Dorais
-/

namespace Batteries

/-- `DArray` is a heterogenous array where the type of each item depends on the index. -/
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
theorem get_mk (i : Fin n) : DArray.get (.mk init) i = init i := rfl

theorem set_mk {α : Fin n → Type _} {init : (i : Fin n) → α i} (i : Fin n) (v : α i) :
    DArray.set (.mk init) i v = .mk fun j => if h : i = j then h ▸ v else init j := rfl

@[simp]
theorem get_set (a : DArray n α) (i : Fin n) (v : α i) : (a.set i v).get i = v := by
  simp only [DArray.get, DArray.set, dif_pos]

theorem get_set_ne (a : DArray n α) (v : α i) (h : i ≠ j) : (a.set i v).get j = a.get j := by
  simp only [DArray.get, DArray.set, dif_neg h]

@[simp]
theorem set_set {α : Fin n → Type _} (a : DArray n α) (i : Fin n)
    (v w : α i) : (a.set i v).set i w = a.set i w := by
  ext j
  if h : i = j then
    rw [← h, get_set, get_set]
  else
    rw [get_set_ne _ _ h, get_set_ne _ _ h, get_set_ne _ _ h]

/-! # Experimental Unsafe Implementation

For this implementation, `DArray n α` is secretly stored as an `Array Unit` with size `n`. This
works because Lean never actually checks that objects have the appropriate type. So it's safe, in
principle, to `unsafeCast` the fake `Unit` or `Array` objects to the appropriate type and similarly
to `unsafeCast` any relevant object to a fake `Unit` or `Array` object.
-/

private unsafe def mkUnsafe (get : (i : Fin n) → α i) : DArray n α :=
  let data : Array Unit := .ofFn fun i => unsafeCast (get i)
  unsafeCast data

private unsafe def getUnsafe (a : DArray n α) (i) : α i :=
  let data : Array Unit := unsafeCast a
  unsafeCast <| data.get ⟨i.val, lcProof⟩

private unsafe def setUnsafe (a : DArray n α) (i) (v : α i) : DArray n α :=
  let data : Array Unit := unsafeCast a
  unsafeCast <| data.set ⟨i.val, lcProof⟩ <| unsafeCast v

private unsafe def recOnUnsafe.{u} {motive : DArray n α → Sort u} (a : DArray n α)
  (h : (get : (i : Fin n) → α i) → motive (.mk get)) : motive a :=
  h a.get

attribute [implemented_by mkUnsafe] DArray.mk
attribute [implemented_by getUnsafe] DArray.get
attribute [implemented_by setUnsafe] DArray.set
attribute [implemented_by recOnUnsafe] DArray.recOn
attribute [implemented_by recOnUnsafe] DArray.casesOn

/-
Copyright (c) 2024 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: François G. Dorais
-/

namespace Batteries

/-!
# Dependent Arrays

`DArray` is a heterogenous array where the type of each item depends on the index. The model
for this type is the dependent function type `(i : Fin n) → α i` where `α i` is the type assigned
to items at index `i`.

The implementation of `DArray` is based on Lean's dynamic array type. This means that the array
values are stored in a contiguous memory region and can be accessed in constant time. Lean's arrays
also support destructive updates when the array is exclusive (RC=1).

### Implementation Details

Lean's array API does not directly support dependent arrays. Each `DArray n α` is internally stored
as an `Array NonScalar` with length `n`. This is sound since Lean's array implementation does not
record nor use the type of the items stored in the array. So it is safe to use `UnsafeCast` to
convert array items to the appropriate type when necessary.
-/

/-- `DArray` is a heterogenous array where the type of each item depends on the index. -/
-- TODO: Use a structure once [lean4#2292](https://github.com/leanprover/lean4/pull/2292) is fixed.
inductive DArray (n) (α : Fin n → Type _) where
  /-- Makes a new `DArray` with given item values. `O(n*g)` where `get i` is `O(g)`. -/
  | mk (get : (i : Fin n) → α i)

namespace DArray

section unsafe_implementation

private unsafe abbrev data : DArray n α → Array NonScalar := unsafeCast

private unsafe def mkImpl (get : (i : Fin n) → α i) : DArray n α :=
  unsafeCast <| Array.ofFn fun i => (unsafeCast (get i) : NonScalar)

private unsafe def getImpl (a : DArray n α) (i) : α i :=
  unsafeCast <| a.data.get ⟨i.val, lcProof⟩

private unsafe def ugetImpl (a : DArray n α) (i : USize) (h : i.toNat < n) : α ⟨i.toNat, h⟩ :=
  unsafeCast <| a.data.uget i lcProof

private unsafe def setImpl (a : DArray n α) (i) (v : α i) : DArray n α :=
  unsafeCast <| a.data.set ⟨i.val, lcProof⟩ <| unsafeCast v

private unsafe def usetImpl (a : DArray n α) (i : USize) (h : i.toNat < n) (v : α ⟨i.toNat, h⟩) :
    DArray n α := unsafeCast <| a.data.uset i (unsafeCast v) lcProof

private unsafe def modifyFImpl [Functor f] (a : DArray n α) (i : Fin n)
    (t : α i → f (α i)) : f (DArray n α) :=
  let v := unsafeCast <| a.data.get ⟨i.val, lcProof⟩
  -- Make sure `v` is unshared, if possible, by replacing its array entry by `box(0)`.
  let a := unsafeCast <| a.data.set ⟨i.val, lcProof⟩ (unsafeCast ())
  setImpl a i <$> t v

private unsafe def umodifyFImpl [Functor f] (a : DArray n α) (i : USize) (h : i.toNat < n)
    (t : α ⟨i.toNat, h⟩ → f (α ⟨i.toNat, h⟩)) : f (DArray n α) :=
  let v := unsafeCast <| a.data.uget i lcProof
  -- Make sure `v` is unshared, if possible, by replacing its array entry by `box(0)`.
  let a := unsafeCast <| a.data.uset i (unsafeCast ()) lcProof
  usetImpl a i h <$> t v

private unsafe def pushImpl (a : DArray n α) (v : β) :
    DArray (n+1) fun i => if h : i.val < n then α ⟨i.val, h⟩ else β :=
  unsafeCast <| a.data.push <| unsafeCast v

private unsafe def popImpl (a : DArray (n+1) α) : DArray n fun i => α i.castSucc :=
  unsafeCast <| a.data.pop

private unsafe def copyImpl (a : DArray n α) : DArray n α :=
  unsafeCast <| a.data.extract 0 n

end unsafe_implementation

attribute [implemented_by mkImpl] DArray.mk

instance (α : Fin n → Type _) [(i : Fin n) → Inhabited (α i)] : Inhabited (DArray n α) where
  default := mk fun _ => default

/-- Gets the `DArray` item at index `i`. `O(1)`. -/
@[implemented_by getImpl]
protected def get : DArray n α → (i : Fin n) → α i
  | mk get => get

@[simp, inherit_doc DArray.get]
protected abbrev getN (a : DArray n α) (i) (h : i < n := by get_elem_tactic) : α ⟨i, h⟩ :=
  a.get ⟨i, h⟩

/-- Gets the `DArray` item at index `i : USize`. Slightly faster than `get`; `O(1)`. -/
@[implemented_by ugetImpl]
protected def uget (a : DArray n α) (i : USize) (h : i.toNat < n) : α ⟨i.toNat, h⟩ :=
  a.get ⟨i.toNat, h⟩

private def casesOnImpl.{u} {motive : DArray n α → Sort u} (a : DArray n α)
    (h : (get : (i : Fin n) → α i) → motive (.mk get)) : motive a :=
  h a.get

attribute [implemented_by casesOnImpl] DArray.casesOn

/-- Sets the `DArray` item at index `i`. `O(1)` if exclusive else `O(n)`. -/
@[implemented_by setImpl]
protected def set (a : DArray n α) (i : Fin n) (v : α i) : DArray n α :=
  mk fun j => if h : i = j then h ▸ v else a.get j

/--
Sets the `DArray` item at index `i : USize`.
Slightly faster than `set` and `O(1)` if exclusive else `O(n)`.
-/
@[implemented_by usetImpl]
protected def uset (a : DArray n α) (i : USize) (h : i.toNat < n) (v : α ⟨i.toNat, h⟩) :=
  a.set ⟨i.toNat, h⟩ v

@[simp, inherit_doc DArray.set]
protected abbrev setN (a : DArray n α) (i) (h : i < n := by get_elem_tactic) (v : α ⟨i, h⟩) :=
  a.set ⟨i, h⟩ v

/-- Modifies the `DArray` item at index `i` using transform `t` and the functor `f`. -/
@[implemented_by modifyFImpl]
protected def modifyF [Functor f] (a : DArray n α) (i : Fin n)
    (t : α i → f (α i)) : f (DArray n α) := a.set i <$> t (a.get i)

/-- Modifies the `DArray` item at index `i` using transform `t`. -/
@[inline]
protected def modify (a : DArray n α) (i : Fin n) (t : α i → α i) : DArray n α :=
  a.modifyF (f:=Id) i t

/-- Modifies the `DArray` item at index `i : USize` using transform `t` and the functor `f`. -/
@[implemented_by umodifyFImpl]
protected def umodifyF [Functor f] (a : DArray n α) (i : USize) (h : i.toNat < n)
    (t : α ⟨i.toNat, h⟩ → f (α ⟨i.toNat, h⟩)) : f (DArray n α) := a.uset i h <$> t (a.uget i h)

/-- Modifies the `DArray` item at index `i : USize` using transform `t`. -/
@[inline]
protected def umodify (a : DArray n α) (i : USize) (h : i.toNat < n)
    (t : α ⟨i.toNat, h⟩ → α ⟨i.toNat, h⟩) : DArray n α :=
  a.umodifyF (f:=Id) i h t

/-- Copies the `DArray` to an exclusive `DArray`. `O(1)` if exclusive else `O(n)`. -/
@[implemented_by copyImpl]
protected def copy (a : DArray n α) : DArray n α := mk a.get

/-- Push an element onto the end of a `DArray`. `O(1)` if exclusive else `O(n)`. -/
@[implemented_by pushImpl]
protected def push (a : DArray n α) (v : β) :
    DArray (n+1) fun i => if h : i.val < n then α ⟨i.val, h⟩ else β :=
  mk fun i => if h : i.val < n then dif_pos h ▸ a.get ⟨i.val, h⟩ else dif_neg h ▸ v

/-- Delete the last item of a `DArray`. `O(1)`. -/
@[implemented_by popImpl]
protected def pop (a : DArray (n+1) α) : DArray n fun i => α i.castSucc :=
  mk fun i => a.get i.castSucc

/-
Copyright (c) 2024 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: François G. Dorais
-/

namespace Batteries

/-- `Object` captures a value of arbitrary type. -/
structure Object where
  /-- Type of the object. -/
  {type : Type _}
  /-- Value of the object. -/
  val : type

namespace Object

@[ext]
protected theorem ext : {a b : Object} → HEq a.val b.val → a = b
  | {..}, {..}, .rfl => rfl

/-- Casts an `Object` to a value of compatible type. -/
protected def cast : (a : Object) → α = a.type → α
  | ⟨a⟩, rfl => a

@[simp]
theorem val_mk (a : α) : Object.val ⟨a⟩ = a := rfl

@[simp]
theorem type_mk (a : α) : Object.type ⟨a⟩ = α := rfl

@[simp]
theorem mk_val (a : Object) : ⟨a.val⟩ = a := rfl

@[simp]
theorem cast_heq_val : (a : Object) → (h : α = a.type) → HEq (a.cast h) a.val
  | {..}, rfl => .rfl

theorem cast_inj : {a b : Object} → {ha : α = a.type} → {hb : α = b.type} →
    a.cast ha = b.cast hb → a = b
  | {..}, {..}, rfl, rfl, rfl => rfl

end Object

/-- `ObjectArray` is a heterogenous array with element types given by `type`. -/
structure ObjectArray (size : Nat) (type : Fin size → Type _) : Type _ where
  private mk_ ::
  /-- Data of an `ObjectArray` represented as `Object`. -/
  data : Array Object
  /-- Data array of `ObjectArray` has correct size. -/
  size_eq : data.size = size
  /-- Data of `ObjectArray` have correct types. -/
  type_eq (i : Fin size) : data[i].type = type i

namespace ObjectArray

/-- Constructs an `ObjectArray` using `init` as inital values. -/
protected def mk (init : (i : Fin size) → type i) : ObjectArray size type where
  data := Array.ofFn fun i => ⟨init i⟩
  size_eq := Array.size_ofFn ..
  type_eq _ := Array.getElem_ofFn .. ▸ rfl

/-- Gets the `ObjectArray` item at index `i`. -/
protected def get (a : ObjectArray size type) (i : Fin size) : type i :=
  have : i < a.data.size := a.size_eq.symm ▸ i.is_lt
  a.data[i].cast (a.type_eq i).symm

/-- Sets the `ObjectArray` item at index `i`. -/
protected def set (a : ObjectArray size type) (i : Fin size) (v : type i) :
    ObjectArray size type where
  data := a.data.set (i.cast a.size_eq.symm) ⟨v⟩
  size_eq := (Array.size_set ..).symm ▸ a.size_eq
  type_eq j := by
    if h : i = j then
      simp [h]
    else
      have h : i.val ≠ j.val := mt Fin.eq_of_val_eq h
      simp [h]
      exact a.type_eq ..

theorem data_getElem {type : Fin size → Type _} (a : ObjectArray size type)
    (i : Nat) (h : i < size) (h' : i < a.data.size) :
    a.data[i] = ⟨a.get ⟨i, h⟩⟩ := by ext; exact Object.cast_heq_val .. |>.symm

theorem data_inj {type : Fin size → Type _} :
    {a b : ObjectArray size type} → a.data = b.data → a = b
  | {..}, {..}, rfl => rfl

@[ext]
protected theorem ext {type : Fin size → Type _} {a b : ObjectArray size type}
    (h : ∀ i, a.get i = b.get i) : a = b := by
  apply data_inj
  apply Array.ext
  · rw [a.size_eq, b.size_eq]
  · intro i hia hib
    have hi : i < size := a.size_eq ▸ hia
    rw [data_getElem a i hi, data_getElem b i hi]
    ext; exact heq_of_eq <| h ..

@[simp]
theorem get_set {type : Fin size → Type _} (a : ObjectArray size type) (i : Fin size) (v : type i) :
    (a.set i v).get i = v := by
  simp [ObjectArray.get, ObjectArray.set]
  exact eq_of_heq <| Object.cast_heq_val ..

theorem get_set_ne {type : Fin size → Type _} (a : ObjectArray size type) (v : type i) (h : i ≠ j) :
    (a.set i v).get j = a.get j := by
  simp [ObjectArray.get, ObjectArray.set]
  congr 1
  apply Array.getElem_set_ne
  apply mt Fin.eq_of_val_eq h

@[simp]
theorem set_set {type : Fin size → Type _} (a : ObjectArray size type) (i : Fin size)
    (v w : type i) : (a.set i v).set i w = a.set i w := by
  ext j
  if h : i = j then
    rw [← h, get_set, get_set]
  else
    rw [get_set_ne _ _ h, get_set_ne _ _ h, get_set_ne _ _ h]

@[simp]
theorem get_mk (i : Fin size) : ObjectArray.get (.mk init) i = init i := by
  simp [ObjectArray.get, ObjectArray.mk]
  exact eq_of_heq <| Object.cast_heq_val ..

theorem set_mk {type : Fin size → Type _} {init} (i : Fin size) (v : type i) :
    ObjectArray.set (.mk init) i v = .mk fun j => if h : i = j then h ▸ v else init j := by
  ext j
  if h : i = j then
    rw [← h, get_set, get_mk, dif_pos rfl]
  else
    rw [get_set_ne _ _ h, get_mk, get_mk, dif_neg h]

end ObjectArray

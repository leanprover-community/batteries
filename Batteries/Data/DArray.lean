/-
Copyright (c) 2024 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: François G. Dorais
-/

import Batteries.Data.Sigma

namespace Batteries

/-- `DArray` is a heterogenous array with element types given by `type`. -/
structure DArray (size : Nat) (type : Fin size → Type _) where
  private mk_ ::
  /-- Data of a `DArray` represented as `Sigma type`. -/
  data : Array (Sigma type)
  /-- Data array of `DArray` has correct size. -/
  size_eq : data.size = size
  /-- Data of `DArray` have correct types. -/
  idx_eq (i : Fin size) : data[i].fst = i

namespace DArray

theorem type_eq {type : Fin size → Type _} {a : DArray size type} (i : Fin size)
    (h : i < a.data.size := a.size_eq.symm ▸ i.is_lt) : a.data[i].type = type i := by
  rw [Sigma.type, a.idx_eq]

/-- Constructs an `DArray` using `init` as inital values. -/
protected def mk (init : (i : Fin size) → type i) : DArray size type where
  data := Array.ofFn fun i => ⟨_, init i⟩
  size_eq := Array.size_ofFn ..
  idx_eq _ := Array.getElem_ofFn .. ▸ rfl

/-- Gets the `DArray` item at index `i`. -/
protected def get (a : DArray size type) (i : Fin size) : type i :=
  have : i < a.data.size := a.size_eq.symm ▸ i.is_lt
  a.data[i].castIdx (a.idx_eq i)

/-- Sets the `DArray` item at index `i`. -/
protected def set (a : DArray size type) (i : Fin size) (v : type i) :
    DArray size type where
  data := a.data.set (i.cast a.size_eq.symm) ⟨_, v⟩
  size_eq := (Array.size_set ..).symm ▸ a.size_eq
  idx_eq j := by
    if h : i = j then
      simp [h]
    else
      have h : i.val ≠ j.val := mt Fin.eq_of_val_eq h
      simp [h]
      exact a.idx_eq ..

theorem data_getElem {type : Fin size → Type _} (a : DArray size type)
    (i : Nat) (h : i < size) (h' : i < a.data.size) :
    a.data[i] = ⟨_, a.get ⟨i, h⟩⟩ := by
  ext
  · congr 1; exact a.idx_eq ⟨i, h⟩
  · exact Sigma.castIdx_heq_val .. |>.symm

theorem data_inj {type : Fin size → Type _} :
    {a b : DArray size type} → a.data = b.data → a = b
  | {..}, {..}, rfl => rfl

@[ext]
protected theorem ext {type : Fin size → Type _} {a b : DArray size type}
    (h : ∀ i, a.get i = b.get i) : a = b := by
  apply data_inj
  apply Array.ext
  · rw [a.size_eq, b.size_eq]
  · intro i hia hib
    have hi : i < size := a.size_eq ▸ hia
    rw [data_getElem a i hi, data_getElem b i hi]
    ext
    · simp
    · exact heq_of_eq <| h ..

@[simp]
theorem get_set {type : Fin size → Type _} (a : DArray size type) (i : Fin size) (v : type i) :
    (a.set i v).get i = v := by
  simp [DArray.get, DArray.set]
  exact eq_of_heq <| Sigma.castIdx_heq_val ..

theorem get_set_ne {type : Fin size → Type _} (a : DArray size type) (v : type i) (h : i ≠ j) :
    (a.set i v).get j = a.get j := by
  simp [DArray.get, DArray.set]
  congr 1
  apply Array.getElem_set_ne
  apply mt Fin.eq_of_val_eq h

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
  exact eq_of_heq <| Sigma.castIdx_heq_val ..

theorem set_mk {type : Fin size → Type _} {init} (i : Fin size) (v : type i) :
    DArray.set (.mk init) i v = .mk fun j => if h : i = j then h ▸ v else init j := by
  ext j
  if h : i = j then
    rw [← h, get_set, get_mk, dif_pos rfl]
  else
    rw [get_set_ne _ _ h, get_mk, get_mk, dif_neg h]

/- Experimental Unsafe Implementation -/

private unsafe def mkUnsafe (init : (i : Fin size) → type i) : DArray size type :=
  let data : Array Unit := .ofFn fun i => unsafeCast (init i)
  unsafeCast data

private unsafe def getUnsafe (a : DArray size type) (i) : type i :=
  let data : Array Unit := unsafeCast a
  unsafeCast <| data[i.val]'(lcProof)

private unsafe def setUnsafe (a : DArray size type) (i) (v : type i) : DArray size type :=
  let data : Array Unit := unsafeCast a
  unsafeCast <| data.set ⟨i.val, lcProof⟩ <| unsafeCast v

private unsafe def dataUnsafe (a : DArray size type) : Array (Sigma type) :=
  .ofFn fun i => ⟨_, a.getUnsafe i⟩

private unsafe def mk_Unsafe {type : Fin size → Type _} (data : Array (Sigma type))
    (size_eq : data.size = size) (idx_eq : ∀ (i : Fin size), data[i].fst = i) : DArray size type :=
  mkUnsafe fun i => idx_eq i ▸ data[i].snd

attribute [implemented_by mk_Unsafe] DArray.mk_
attribute [implemented_by mkUnsafe] DArray.mk
attribute [implemented_by dataUnsafe] DArray.data
attribute [implemented_by getUnsafe] DArray.get
attribute [implemented_by setUnsafe] DArray.set

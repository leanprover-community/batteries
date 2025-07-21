/-
Copyright (c) 2023 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: François G. Dorais
-/
import Batteries.Tactic.Alias

namespace ByteArray

attribute [ext] ByteArray

instance : DecidableEq ByteArray :=
  fun _ _ => decidable_of_decidable_of_iff ByteArray.ext_iff.symm

theorem getElem_eq_data_getElem (a : ByteArray) (h : i < a.size) : a[i] = a.data[i] := rfl

/-! ### uget/uset -/

@[simp] theorem uset_eq_set (a : ByteArray) {i : USize} (h : i.toNat < a.size) (v : UInt8) :
    a.uset i v h = a.set i.toNat v := rfl

/-! ### empty -/

@[simp] theorem data_mkEmpty (cap) : (emptyWithCapacity cap).data = #[] := rfl

@[simp] theorem data_empty : empty.data = #[] := rfl

@[simp] theorem size_empty : empty.size = 0 := rfl

/-! ### push -/

@[simp] theorem data_push (a : ByteArray) (b : UInt8) : (a.push b).data = a.data.push b := rfl

@[simp] theorem size_push (a : ByteArray) (b : UInt8) : (a.push b).size = a.size + 1 :=
  Array.size_push ..

@[simp] theorem get_push_eq (a : ByteArray) (x : UInt8) : (a.push x)[a.size] = x :=
  Array.getElem_push_eq ..

theorem get_push_lt (a : ByteArray) (x : UInt8) (i : Nat) (h : i < a.size) :
    (a.push x)[i]'(size_push .. ▸ Nat.lt_succ_of_lt h) = a[i] :=
  Array.getElem_push_lt ..

/-! ### set -/

@[simp] theorem data_set (a : ByteArray) (i : Fin a.size) (v : UInt8) :
    (a.set i v).data = a.data.set i v i.isLt := rfl

@[simp] theorem size_set (a : ByteArray) (i : Fin a.size) (v : UInt8) :
    (a.set i v).size = a.size :=
  Array.size_set ..

@[simp] theorem get_set_eq (a : ByteArray) (i : Fin a.size) (v : UInt8) : (a.set i v)[i.val] = v :=
  Array.getElem_set_self _

theorem get_set_ne (a : ByteArray) (i : Fin a.size) (v : UInt8) (hj : j < a.size) (h : i.val ≠ j) :
    (a.set i v)[j]'(a.size_set .. ▸ hj) = a[j] :=
  Array.getElem_set_ne (h := h) ..

theorem set_set (a : ByteArray) (i : Fin a.size) (v v' : UInt8) :
    (a.set i v).set i v' = a.set i v' :=
  ByteArray.ext <| Array.set_set ..

/-! ### copySlice -/

@[simp] theorem data_copySlice (a i b j len exact) :
  (copySlice a i b j len exact).data = b.data.extract 0 j ++ a.data.extract i (i + len)
    ++ b.data.extract (j + min len (a.data.size - i)) b.data.size := rfl

/-! ### append -/

@[simp] theorem append_eq (a b) : ByteArray.append a b = a ++ b := rfl

@[simp] theorem data_append (a b : ByteArray) : (a ++ b).data = a.data ++ b.data := by
  rw [←append_eq]; simp [ByteArray.append, size]
  rw [Array.extract_empty_of_stop_le_start (h:=Nat.le_add_right ..), Array.append_empty]

theorem size_append (a b : ByteArray) : (a ++ b).size = a.size + b.size := by
  simp only [size, append_eq, data_append]; exact Array.size_append ..

theorem get_append_left {a b : ByteArray} (hlt : i < a.size)
    (h : i < (a ++ b).size := size_append .. ▸ Nat.lt_of_lt_of_le hlt (Nat.le_add_right ..)) :
    (a ++ b)[i] = a[i] := by
  simp [getElem_eq_data_getElem]; exact Array.getElem_append_left hlt

theorem get_append_right {a b : ByteArray} (hle : a.size ≤ i) (h : i < (a ++ b).size)
    (h' : i - a.size < b.size := Nat.sub_lt_left_of_lt_add hle (size_append .. ▸ h)) :
    (a ++ b)[i] = b[i - a.size] := by
  simp [getElem_eq_data_getElem]; exact Array.getElem_append_right hle

/-! ### extract -/

@[simp] theorem data_extract (a : ByteArray) (start stop) :
    (a.extract start stop).data = a.data.extract start stop := by
  simp [extract]
  match Nat.le_total start stop with
  | .inl h => simp [h, Nat.add_sub_cancel']
  | .inr h => simp [h, Nat.sub_eq_zero_of_le, Array.extract_empty_of_stop_le_start]

@[simp] theorem size_extract (a : ByteArray) (start stop) :
    (a.extract start stop).size = min stop a.size - start := by
  simp [size]

theorem get_extract_aux {a : ByteArray} {start stop} (h : i < (a.extract start stop).size) :
    start + i < a.size := by
  apply Nat.add_lt_of_lt_sub'; apply Nat.lt_of_lt_of_le h
  rw [size_extract, ← Nat.sub_min_sub_right]; exact Nat.min_le_right ..

@[simp] theorem get_extract {a : ByteArray} {start stop} (h : i < (a.extract start stop).size) :
    (a.extract start stop)[i] = a[start+i]'(get_extract_aux h) := by
  simp [getElem_eq_data_getElem]

/-! ### ofFn -/

/--- `ofFn f` with `f : Fin n → UInt8` returns the byte array whose `i`th element is `f i`. --/
@[inline] def ofFn (f : Fin n → UInt8) : ByteArray :=
  Fin.foldl n (fun acc i => acc.push (f i)) (emptyWithCapacity n)

@[simp] theorem ofFn_zero (f : Fin 0 → UInt8) : ofFn f = empty := rfl

theorem ofFn_succ (f : Fin (n+1) → UInt8) :
    ofFn f = (ofFn fun i => f i.castSucc).push (f (Fin.last n)) := by
  simp [ofFn, Fin.foldl_succ_last, emptyWithCapacity]

@[simp] theorem data_ofFn (f : Fin n → UInt8) : (ofFn f).data = .ofFn f := by
  induction n with
  | zero => rfl
  | succ n ih => simp [ofFn_succ, Array.ofFn_succ, ih, Fin.last]

@[simp] theorem size_ofFn (f : Fin n → UInt8) : (ofFn f).size = n := by
  simp [size]

@[simp] theorem get_ofFn (f : Fin n → UInt8) (i : Fin (ofFn f).size) :
    (ofFn f).get i = f (i.cast (size_ofFn f)) := by
  simp [get, Fin.cast]

@[simp] theorem getElem_ofFn (f : Fin n → UInt8) (i) (h : i < (ofFn f).size) :
    (ofFn f)[i] = f ⟨i, size_ofFn f ▸ h⟩ := get_ofFn f ⟨i, h⟩

/-! ### map/mapM -/

/--
Unsafe optimized implementation of `mapM`.

This function is unsafe because it relies on the implementation limit that the size of an array is
always less than `USize.size`.
-/
@[inline]
unsafe def mapMUnsafe [Monad m] (a : ByteArray) (f : UInt8 → m UInt8) : m ByteArray :=
  loop a 0 a.usize
where
  /-- Inner loop for `mapMUnsafe`. -/
  @[specialize]
  loop (a : ByteArray) (k s : USize) := do
    if k < a.usize then
      let x := a.uget k lcProof
      let y ← f x
      let a := a.uset k y lcProof
      loop a (k+1) s
    else pure a

/-- `mapM f a` applies the monadic function `f` to each element of the array. -/
@[implemented_by mapMUnsafe]
def mapM [Monad m] (a : ByteArray) (f : UInt8 → m UInt8) : m ByteArray := do
  let mut r := a
  for i in [0:r.size] do
    r := r.set! i (← f r[i]!)
  return r

/-- `map f a` applies the function `f` to each element of the array. -/
@[inline]
def map (a : ByteArray) (f : UInt8 → UInt8) : ByteArray :=
  mapM (m:=Id) a f

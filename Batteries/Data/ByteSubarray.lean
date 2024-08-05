
/-
Copyright (c) 2021 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, François G. Dorais
-/

namespace Batteries

/-- A subarray of a `ByteArray`. -/
structure ByteSubarray where
  /-- `O(1)`. Get data array of a `ByteSubarray`. -/
  array : ByteArray
  /-- `O(1)`. Get start index of a `ByteSubarray`. -/
  start : Nat
  /-- `O(1)`. Get stop index of a `ByteSubarray`. -/
  stop : Nat
  /-- Start index is before stop index. -/
  start_le_stop : start ≤ stop
  /-- Stop index is before end of data array. -/
  stop_le_array_size : stop ≤ array.size

namespace ByteSubarray

/-- `O(1)`. Get the size of a `ByteSubarray`. -/
protected def size (self : ByteSubarray) := self.stop - self.start

/-- `O(1)`. Test if a `ByteSubarray` is empty. -/
protected def isEmpty (self : ByteSubarray) := self.start != self.stop

theorem stop_eq_start_add_size (self : ByteSubarray) : self.stop = self.start + self.size := by
  rw [ByteSubarray.size, Nat.add_sub_cancel' self.start_le_stop]

/-- `O(n)`. Extract a `ByteSubarray` to a `ByteArray`. -/
def toByteArray (self : ByteSubarray) : ByteArray :=
  self.array.extract self.start self.stop

/-- `O(1)`. Get the element at index `i` from the start of a `ByteSubarray`. -/
@[inline] def get (self : ByteSubarray) (i : Fin self.size) : UInt8 :=
  have : self.start + i.1 < self.array.size := by
    apply Nat.lt_of_lt_of_le _ self.stop_le_array_size
    rw [stop_eq_start_add_size]
    apply Nat.add_lt_add_left i.is_lt self.start
  self.array[self.start + i.1]

instance : GetElem ByteSubarray Nat UInt8 fun self i => i < self.size where
  getElem self i h := self.get ⟨i, h⟩

/-- `O(1)`. Pop the last element of a `ByteSubarray`. -/
@[inline] def pop (self : ByteSubarray) : ByteSubarray :=
  if h : self.start = self.stop then self else
    {self with
      stop := self.stop - 1
      start_le_stop := Nat.le_pred_of_lt (Nat.lt_of_le_of_ne self.start_le_stop h)
      stop_le_array_size := Nat.le_trans (Nat.pred_le _) self.stop_le_array_size
    }

/-- `O(1)`. Pop the first element of a `ByteSubarray`. -/
@[inline] def popFront (self : ByteSubarray) : ByteSubarray :=
  if h : self.start = self.stop then self else
    {self with
      start := self.start + 1
      start_le_stop := Nat.succ_le_of_lt (Nat.lt_of_le_of_ne self.start_le_stop h)
    }

/-- Folds a monadic function over a `ByteSubarray` from left to right. -/
@[inline] def foldlM [Monad m] (self : ByteSubarray) (f : β → UInt8 → m β) (init : β) : m β :=
  self.array.foldlM f init self.start self.stop

/-- Folds a function over a `ByteSubarray` from left to right. -/
@[inline] def foldl (self : ByteSubarray) (f : β → UInt8 → β) (init : β) : β :=
  self.foldlM (m:=Id) f init

/-- Implementation of `forIn` for a `ByteSubarray`. -/
@[specialize]
protected def forIn [Monad m] (self : ByteSubarray) (init : β) (f : UInt8 → β → m (ForInStep β)) :
    m β := loop self.size (Nat.le_refl _) init
where
  /-- Inner loop of the `forIn` implementation for `ByteSubarray`. -/
  loop (i : Nat) (h : i ≤ self.size) (b : β) : m β := do
    match i, h with
    | 0,   _ => pure b
    | i+1, h =>
      match (← f self[self.size - 1 - i] b) with
      | ForInStep.done b  => pure b
      | ForInStep.yield b => loop i (Nat.le_of_succ_le h) b

instance : ForIn m ByteSubarray UInt8 where
  forIn := ByteSubarray.forIn

instance : Stream ByteSubarray UInt8 where
  next? s := s[0]? >>= fun x => (x, s.popFront)

end Batteries.ByteSubarray

/-- `O(1)`. Coerce a byte array into a byte slice. -/
def ByteArray.toByteSubarray (array : ByteArray) : Batteries.ByteSubarray where
  array := array
  start := 0
  stop := array.size
  start_le_stop := Nat.zero_le _
  stop_le_array_size := Nat.le_refl _

instance : Coe ByteArray Batteries.ByteSubarray where
  coe := ByteArray.toByteSubarray

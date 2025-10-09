
/-
Copyright (c) 2021 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, François G. Dorais
-/
import Std

namespace ByteSlice

/-- Test whether a byte slice is empty. -/
protected abbrev isEmpty (s : ByteSlice) := s.start == s.stop

theorem stop_eq_start_add_size (s : ByteSlice) : s.stop = s.start + s.size := by
  rw [ByteSlice.size, Nat.add_sub_cancel' s.start_le_stop]

/-- Returns the subslice obtained by removing the last element. -/
abbrev pop (s : ByteSlice) : ByteSlice :=
  s.slice 0 (s.size - 1)

/-- Returns the subslice obtained by removing the first element. -/
abbrev popFront (s : ByteSlice) : ByteSlice :=
  s.slice 1 s.size

/-- Folds a monadic function over a `ByteSubarray` from left to right. -/
@[inline]
def foldlM [Monad m] (s : ByteSlice) (f : β → UInt8 → m β) (init : β) : m β :=
  s.toByteArray.foldlM f init s.start s.stop

/-- Folds a function over a `ByteSubarray` from left to right. -/
@[inline]
def foldl (s : ByteSlice) (f : β → UInt8 → β) (init : β) : β :=
  s.foldlM (m:=Id) f init

/-- Implementation of `forIn` for a `ByteSlice`. -/
@[specialize]
protected def forIn [Monad m] (s : ByteSlice) (init : β) (f : UInt8 → β → m (ForInStep β)) :
    m β := loop s.size (Nat.le_refl _) init
where
  /-- Inner loop of the `forIn` implementation for `ByteSlice`. -/
  loop (i : Nat) (h : i ≤ s.size) (b : β) : m β := do
    match i, h with
    | 0,   _ => pure b
    | i+1, h =>
      match (← f s[s.size - 1 - i] b) with
      | ForInStep.done b  => pure b
      | ForInStep.yield b => loop i (Nat.le_of_succ_le h) b

instance : ForIn m ByteSlice UInt8 where
  forIn := ByteSlice.forIn

instance : Stream ByteSlice UInt8 where
  next? s := s[0]? >>= (·, s.popFront)

instance : Coe ByteArray ByteSlice where
  coe := ByteArray.toByteSlice

end ByteSlice

namespace Batteries

/-- A subarray of a `ByteArray`. -/
@[deprecated ByteSlice (since := "2025-10-04")]
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
set_option linter.deprecated false

attribute [deprecated ByteSlice.byteArray (since := "2025-10-04")]
  ByteSubarray.array

attribute [deprecated ByteSlice.start (since := "2025-10-04")]
  ByteSubarray.start

attribute [deprecated ByteSlice.stop (since := "2025-10-04")]
  ByteSubarray.stop

attribute [deprecated ByteSlice.start_le_stop (since := "2025-10-04")]
  ByteSubarray.start_le_stop

attribute [deprecated ByteSlice.stop_le_size_byteArray (since := "2025-10-04")]
  ByteSubarray.stop_le_array_size

/-- `O(1)`. Get the size of a `ByteSubarray`. -/
@[deprecated ByteSlice.size (since := "2025-10-04")]
protected def size (self : ByteSubarray) := self.stop - self.start

/-- `O(1)`. Test if a `ByteSubarray` is empty. -/
@[deprecated ByteSlice.isEmpty (since := "2025-10-04")]
protected def isEmpty (self : ByteSubarray) := self.start == self.stop

@[deprecated ByteSlice.stop_eq_start_add_size (since := "2025-10-04")]
theorem stop_eq_start_add_size (self : ByteSubarray) : self.stop = self.start + self.size := by
  rw [ByteSubarray.size, Nat.add_sub_cancel' self.start_le_stop]

/-- `O(n)`. Extract a `ByteSubarray` to a `ByteArray`. -/
@[deprecated ByteSlice.toByteArray (since := "2025-10-04")]
def toByteArray (self : ByteSubarray) : ByteArray :=
  self.array.extract self.start self.stop

/-- `O(1)`. Get the element at index `i` from the start of a `ByteSubarray`. -/
@[deprecated ByteSlice.get (since := "2025-10-04"), inline]
def get (self : ByteSubarray) (i : Fin self.size) : UInt8 :=
  have : self.start + i.1 < self.array.size := by
    apply Nat.lt_of_lt_of_le _ self.stop_le_array_size
    rw [stop_eq_start_add_size]
    apply Nat.add_lt_add_left i.is_lt self.start
  self.array[self.start + i.1]

instance : GetElem ByteSubarray Nat UInt8 fun self i => i < self.size where
  getElem self i h := self.get ⟨i, h⟩

/-- `O(1)`. Pop the last element of a `ByteSubarray`. -/
@[deprecated ByteSlice.pop (since := "2025-10-04"), inline]
def pop (self : ByteSubarray) : ByteSubarray :=
  if h : self.start = self.stop then self else
    {self with
      stop := self.stop - 1
      start_le_stop := Nat.le_pred_of_lt (Nat.lt_of_le_of_ne self.start_le_stop h)
      stop_le_array_size := Nat.le_trans (Nat.pred_le _) self.stop_le_array_size
    }

/-- `O(1)`. Pop the first element of a `ByteSubarray`. -/
@[deprecated ByteSlice.popFront (since := "2025-10-04"), inline]
def popFront (self : ByteSubarray) : ByteSubarray :=
  if h : self.start = self.stop then self else
    {self with
      start := self.start + 1
      start_le_stop := Nat.succ_le_of_lt (Nat.lt_of_le_of_ne self.start_le_stop h)
    }

/-- Folds a monadic function over a `ByteSubarray` from left to right. -/
@[deprecated ByteSlice.foldlM (since := "2025-10-04"), inline]
def foldlM [Monad m] (self : ByteSubarray) (f : β → UInt8 → m β) (init : β) : m β :=
  self.array.foldlM f init self.start self.stop

/-- Folds a function over a `ByteSubarray` from left to right. -/
@[deprecated ByteSlice.foldl (since := "2025-10-04"), inline]
def foldl (self : ByteSubarray) (f : β → UInt8 → β) (init : β) : β :=
  self.foldlM (m:=Id) f init

/-- Implementation of `forIn` for a `ByteSubarray`. -/
@[specialize]
--@[deprecated ByteSlice.forIn (since := "2025-10-04"), specialize]
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

instance : Std.Stream ByteSubarray UInt8 where
  next? s := s[0]? >>= fun x => (x, s.popFront)

end Batteries.ByteSubarray

set_option linter.deprecated false in
/-- `O(1)`. Coerce a byte array into a byte slice. -/
@[deprecated ByteArray.toByteSlice (since := "2025-10-04")]
def ByteArray.toByteSubarray (array : ByteArray) : Batteries.ByteSubarray where
  array := array
  start := 0
  stop := array.size
  start_le_stop := Nat.zero_le _
  stop_le_array_size := Nat.le_refl _

set_option linter.deprecated false in
instance : Coe ByteArray Batteries.ByteSubarray where
  coe := ByteArray.toByteSubarray

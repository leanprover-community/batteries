
/-
Copyright (c) 2021 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, François G. Dorais
-/
module

public import Std.Data.ByteSlice
import all Std.Data.ByteSlice  -- for unfolding `ByteSlice.size`

namespace ByteSlice

/-- Test whether a byte slice is empty. -/
public protected abbrev isEmpty (s : ByteSlice) := s.start == s.stop

public theorem stop_eq_start_add_size (s : ByteSlice) : s.stop = s.start + s.size := by
  rw [ByteSlice.size, Nat.add_sub_cancel' s.start_le_stop]

/-- Returns the subslice obtained by removing the last element. -/
public abbrev pop (s : ByteSlice) : ByteSlice :=
  s.slice 0 (s.size - 1)

/-- Returns the subslice obtained by removing the first element. -/
public abbrev popFront (s : ByteSlice) : ByteSlice :=
  s.slice 1 s.size

/-- Folds a monadic function over a `ByteSubarray` from left to right. -/
@[inline]
public def foldlM [Monad m] (s : ByteSlice) (f : β → UInt8 → m β) (init : β) : m β :=
  s.toByteArray.foldlM f init s.start s.stop

/-- Folds a function over a `ByteSubarray` from left to right. -/
@[inline]
public def foldl (s : ByteSlice) (f : β → UInt8 → β) (init : β) : β :=
  s.foldlM (m:=Id) f init

/-- Implementation of `forIn` for a `ByteSlice`. -/
@[specialize]
public protected def forIn [Monad m] (s : ByteSlice) (init : β) (f : UInt8 → β → m (ForInStep β)) :
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

public instance [Monad m] : ForIn m ByteSlice UInt8 where
  forIn := ByteSlice.forIn

public instance : Std.Stream ByteSlice UInt8 where
  next? s := s[0]? >>= (·, s.popFront)

public instance : Coe ByteArray ByteSlice where
  coe := ByteArray.toByteSlice

end ByteSlice

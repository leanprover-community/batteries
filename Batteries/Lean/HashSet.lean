/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Std.Data.HashSet

namespace Std.HashSet

variable [BEq α] [Hashable α]

/--
`O(n)`. Returns `true` if `f` returns `true` for any element of the set.
-/
@[specialize]
def anyM [Monad m] (s : HashSet α) (f : α → m Bool) : m Bool := do
  for a in s do
    if ← f a then
      return true
  return false

/--
`O(n)`. Returns `true` if `f` returns `true` for all elements of the set.
-/
@[specialize]
def allM [Monad m] (s : HashSet α) (f : α → m Bool) : m Bool := do
  for a in s do
    if !(← f a) then
      return false
  return true

instance : BEq (HashSet α) where
  beq s t := s.all (t.contains ·) && t.all (s.contains ·)

/--
`O(1)` amortized. Similar to `insert`, but also returns a Boolean flag indicating whether an
existing entry has been replaced with `a => b`.
-/
@[inline, deprecated containsThenInsert (since := "2024-09-17")]
def insert' (s : HashSet α) (a : α) : HashSet α × Bool :=
  let oldSize := s.size
  let s := s.insert a
  (s, s.size == oldSize)

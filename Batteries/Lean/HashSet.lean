/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Lean.Data.HashSet

namespace Lean.HashSet

variable [BEq α] [Hashable α]

instance : Singleton α (HashSet α) := ⟨fun x => HashSet.empty.insert x⟩
instance : Insert α (HashSet α) := ⟨fun a s => s.insert a⟩

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
`O(n)`. Returns `true` if `f` returns `true` for any element of the set.
-/
@[inline]
def any (s : HashSet α) (f : α → Bool) : Bool :=
  Id.run <| s.anyM f

/--
`O(n)`. Returns `true` if `f` returns `true` for all elements of the set.
-/
@[specialize]
def allM [Monad m] (s : HashSet α) (f : α → m Bool) : m Bool := do
  for a in s do
    if !(← f a) then
      return false
  return true

/--
`O(n)`. Returns `true` if `f` returns `true` for all elements of the set.
-/
@[inline]
def all (s : HashSet α) (f : α → Bool) : Bool :=
  Id.run <| s.allM f

instance : BEq (HashSet α) where
  beq s t := s.all (t.contains ·) && t.all (s.contains ·)

/--
`O(1)` amortized. Similar to `insert`, but also returns a Boolean flag indicating whether an
existing entry has been replaced with `a => b`.
-/
@[inline]
def insert' (s : HashSet α) (a : α) : HashSet α × Bool :=
  let oldSize := s.size
  let s := s.insert a
  (s, s.size == oldSize)

/--
`O(n)`. Obtain a `HashSet` from an array.
-/
@[inline]
protected def ofArray [BEq α] [Hashable α] (as : Array α) : HashSet α :=
  HashSet.empty.insertMany as

/--
`O(n)`. Obtain a `HashSet` from a list.
-/
@[inline]
protected def ofList [BEq α] [Hashable α] (as : List α) : HashSet α :=
  HashSet.empty.insertMany as

/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Lean.Data.PersistentHashSet

namespace Lean.PersistentHashSet

variable [BEq α] [Hashable α]

instance : ForIn m (PersistentHashSet α) α where
  forIn s init step := do
    let mut state := init
    for (k, _) in s.set do
      match ← step k state with
      | .done state' => return state'
      | .yield state' => state := state'
    return state

/--
Returns `true` if `f` returns `true` for any element of the set.
-/
@[specialize]
def anyM [Monad m] (s : PersistentHashSet α) (f : α → m Bool) : m Bool := do
  for a in s do
    if ← f a then
      return true
  return false

/--
Returns `true` if `f` returns `true` for any element of the set.
-/
@[inline]
def any (s : PersistentHashSet α) (f : α → Bool) : Bool :=
  Id.run <| s.anyM f

/--
Returns `true` if `f` returns `true` for all elements of the set.
-/
@[specialize]
def allM [Monad m] (s : PersistentHashSet α) (f : α → m Bool) : m Bool := do
  for a in s do
    if ! (← f a) then
      return false
  return true

/--
Returns `true` if `f` returns `true` for all elements of the set.
-/
@[inline]
def all (s : PersistentHashSet α) (f : α → Bool) : Bool :=
  Id.run <| s.allM f

instance : BEq (PersistentHashSet α) where
  beq s t := s.all (t.contains ·) && t.all (s.contains ·)

/--
Insert all elements from a collection into a `PersistentHashSet`.
-/
def insertMany [ForIn Id ρ α] (s : PersistentHashSet α) (as : ρ) :
    PersistentHashSet α := Id.run do
  let mut s := s
  for a in as do
    s := s.insert a
  return s

/--
Obtain a `PersistentHashSet` from an array.
-/
@[inline]
protected def ofArray [BEq α] [Hashable α] (as : Array α) : PersistentHashSet α :=
  PersistentHashSet.empty.insertMany as

/--
Obtain a `PersistentHashSet` from a list.
-/
@[inline]
protected def ofList [BEq α] [Hashable α] (as : List α) : PersistentHashSet α :=
  PersistentHashSet.empty.insertMany as

/--
Merge two `PersistentHashSet`s.
-/
@[inline]
def merge (s t : PersistentHashSet α) : PersistentHashSet α :=
  s.insertMany t

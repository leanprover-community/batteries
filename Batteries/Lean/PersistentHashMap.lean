/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Lean.Data.PersistentHashMap

namespace Lean.PersistentHashMap

variable [BEq α] [Hashable α]

/--
Builds a `PersistentHashMap` from a list of key-value pairs. Values of
duplicated keys are replaced by their respective last occurrences.
-/
def ofList (xs : List (α × β)) : PersistentHashMap α β :=
  xs.foldl (init := {}) fun m (k, v) => m.insert k v

/--
Variant of `ofList` which accepts a function that combines values of duplicated
keys.
-/
def ofListWith (xs : List (α × β)) (f : α → β → β → β) :
    PersistentHashMap α β :=
  xs.foldl (init := {}) fun m (k, v) =>
    match m.find? k with
    | none    => m.insert k v
    | some v' => m.insert k <| f k v v'

/--
Builds a `PersistentHashMap` from an array of key-value pairs. Values of
duplicated keys are replaced by their respective last occurrences.
-/
def ofArray (xs : Array (α × β)) : PersistentHashMap α β :=
  xs.foldl (init := {}) fun m (k, v) => m.insert k v

/--
Variant of `ofArray` which accepts a function that combines values of duplicated
keys.
-/
def ofArrayWith (xs : Array (α × β)) (f : α → β → β → β) :
    PersistentHashMap α β :=
  xs.foldl (init := {}) fun m (k, v) =>
    match m.find? k with
    | none    => m.insert k v
    | some v' => m.insert k <| f k v v'

/--
Merge two `PersistentHashMap`s. The values of keys which appear in both maps are
combined using the monadic function `f`.
-/
@[specialize]
def mergeWithM [Monad m] (self other : PersistentHashMap α β)
    (f : α → β → β → m β) : m (PersistentHashMap α β) :=
  other.foldlM (init := self) fun map k v₂ =>
    match map.find? k with
    | none => return map.insert k v₂
    | some v₁ => return map.insert k (← f k v₁ v₂)

/--
Merge two `PersistentHashMap`s. The values of keys which appear in both maps are
combined using `f`.
-/
@[inline]
def mergeWith (self other : PersistentHashMap α β) (f : α → β → β → β) :
    PersistentHashMap α β :=
  -- Implementing this function directly, rather than via `mergeWithM`, gives
  -- us less constrained universes.
  other.foldl (init := self) fun map k v₂ =>
    match map.find? k with
    | none => map.insert k v₂
    | some v₁ => map.insert k <| f k v₁ v₂

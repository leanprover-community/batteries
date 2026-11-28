/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/
module

public import Std.Data.HashMap.Basic

public section
namespace Std.HashMap

variable [BEq α] [Hashable α]

/--
`O(|other|)` amortized. Merge two `HashMap`s.
The values of keys which appear in both maps are combined using the monadic function `f`.
-/
@[specialize]
def mergeWithM {m α β} [BEq α] [Hashable α] [Monad m] (f : α → β → β → m β)
    (self other : HashMap α β) : m (HashMap α β) :=
  other.foldM (init := self) fun map k v₂ =>
    match map[k]? with
    | none => return map.insert k v₂
    | some v₁ => return map.insert k (← f k v₁ v₂)

/--
`O(|other|)` amortized. Merge two `HashMap`s.
The values of keys which appear in both maps are combined using `f`.
-/
@[inline]
def mergeWith (f : α → β → β → β) (self other : HashMap α β) : HashMap α β :=
  -- Implementing this function directly, rather than via `mergeWithM`, gives
  -- us less constrained universes.
  other.fold (init := self) fun map k v₂ =>
    match map[k]? with
    | none => map.insert k v₂
    | some v₁ => map.insert k <| f k v₁ v₂

/--
Given a key `a`, returns a key-value pair in the map whose key compares equal to `a`.
Note that the returned key may not be identical to the input, if `==` ignores some part
of the value.
```
def hashMap := ofList [("one", 1), ("two", 2)]
hashMap.findEntry? "one" = some ("one", 1)
hashMap.findEntry? "three" = none
```
-/
-- This could be given a more efficient low level implementation.
@[inline]
def findEntry? [BEq α] [Hashable α] (m : Std.HashMap α β) (k : α) : Option (α × β) :=
  if h : k ∈ m then some (m.getKey k h, m.get k h) else none

/--
Variant of `ofList` which accepts a function that combines values of duplicated keys.
```
ofListWith [("one", 1), ("one", 2)] (fun v₁ v₂ => v₁ + v₂) = {"one" => 3}
```
-/
def ofListWith [BEq α] [Hashable α] (l : List (α × β)) (f : β → β → β) : HashMap α β :=
  l.foldl (init := ∅) fun m p =>
    match m[p.1]? with
    | none   => m.insert p.1 p.2
    | some v => m.insert p.1 <| f v p.2

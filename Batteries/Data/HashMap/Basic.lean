/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Mario Carneiro
-/
import Std.Data.HashMap

namespace Batteries.HashMap

/-- A hash is lawful if elements which compare equal under `==` have equal hash. -/
class LawfulHashable (α : Type _) [BEq α] [Hashable α] : Prop where
  /-- Two elements which compare equal under the `BEq` instance have equal hash. -/
  hash_eq {a b : α} : a == b → hash a = hash b

/--
`HashMap α β` is a key-value map which stores elements in an array using a hash function
to find the values. This allows it to have very good performance for lookups
(average `O(1)` for a perfectly random hash function), but it is not a persistent data structure,
meaning that one should take care to use the map linearly when performing updates.
Copies are `O(n)`.
-/
abbrev _root_.Batteries.HashMap (α : Type u) (β : Type v) [BEq α] [Hashable α] := Std.HashMap α β

/-- Make a new hash map with the specified capacity. -/
@[inline] def _root_.Batteries.mkHashMap [BEq α] [Hashable α] (capacity := 0) : HashMap α β :=
  ⟨.emptyWithCapacity capacity, .emptyWithCapacity⟩

instance [BEq α] [Hashable α] : Inhabited (HashMap α β) where
  default := mkHashMap

instance [BEq α] [Hashable α] : EmptyCollection (HashMap α β) := ⟨mkHashMap⟩

/--
Make a new empty hash map.
```
(empty : Batteries.HashMap Int Int).toList = []
```
-/
@[inline] def empty [BEq α] [Hashable α] : HashMap α β := mkHashMap

variable {_ : BEq α} {_ : Hashable α}

/--
The number of elements in the hash map.
```
(ofList [("one", 1), ("two", 2)]).size = 2
```
-/
@[inline] def size (self : HashMap α β) : Nat := Std.HashMap.size self

/--
Is the map empty?
```
(empty : Batteries.HashMap Int Int).isEmpty = true
(ofList [("one", 1), ("two", 2)]).isEmpty = false
```
-/
@[inline] def isEmpty (self : HashMap α β) : Bool := Std.HashMap.isEmpty self

/--
Inserts key-value pair `a, b` into the map.
If an element equal to `a` is already in the map, it is replaced by `b`.
```
def hashMap := ofList [("one", 1), ("two", 2)]
hashMap.insert "three" 3 = {"one" => 1, "two" => 2, "three" => 3}
hashMap.insert "two" 0 = {"one" => 1, "two" => 0}
```
-/
@[inline] def insert (self : HashMap α β) (a : α) (b : β) : HashMap α β :=
  Std.HashMap.insert self a b

/--
Similar to `insert`, but also returns a boolean flag indicating whether an existing entry has been
replaced with `a => b`.
```
def hashMap := ofList [("one", 1), ("two", 2)]
hashMap.insert' "three" 3 = ({"one" => 1, "two" => 2, "three" => 3}, false)
hashMap.insert' "two" 0 = ({"one" => 1, "two" => 0}, true)
```
-/
@[inline] def insert' (m : HashMap α β) (a : α) (b : β) : HashMap α β × Bool :=
  Prod.swap <|Std.HashMap.containsThenInsert m a b

/--
Removes key `a` from the map. If it does not exist in the map, the map is returned unchanged.
```
def hashMap := ofList [("one", 1), ("two", 2)]
hashMap.erase "one" = {"two" => 2}
hashMap.erase "three" = {"one" => 1, "two" => 2}
```
-/
@[inline] def erase (self : HashMap α β) (a : α) : HashMap α β := Std.HashMap.erase self a

/--
Performs an in-place edit of the value, ensuring that the value is used linearly.
The function `f` is passed the original key of the entry, along with the value in the map.
```
(ofList [("one", 1), ("two", 2)]).modify "one" (fun _ v => v + 1) = {"one" => 2, "two" => 2}
(ofList [("one", 1), ("two", 2)]).modify "three" (fun _ v => v + 1) = {"one" => 1, "two" => 2}
```
-/
@[inline] def modify (self : HashMap α β) (a : α) (f : α → β → β) : HashMap α β :=
  Std.HashMap.modify self a (f a)

/--
Looks up an element in the map with key `a`.
```
def hashMap := ofList [("one", 1), ("two", 2)]
hashMap.find? "one" = some 1
hashMap.find? "three" = none
```
-/
@[inline] def find? (self : HashMap α β) (a : α) : Option β := self[a]?

/--
Looks up an element in the map with key `a`. Returns `b₀` if the element is not found.
```
def hashMap := ofList [("one", 1), ("two", 2)]
hashMap.findD "one" 0 = 1
hashMap.findD "three" 0 = 0
```
-/
@[inline] def findD (self : HashMap α β) (a : α) (b₀ : β) : β := self.getD a b₀

/--
Looks up an element in the map with key `a`. Panics if the element is not found.
```
def hashMap := ofList [("one", 1), ("two", 2)]
hashMap.find! "one" = 1
hashMap.find! "three" => panic!
```
-/
@[inline] def find! [Inhabited β] (self : HashMap α β) (a : α) : β :=
  self.getD a (panic! "key is not in the map")

instance : GetElem (HashMap α β) α (Option β) fun _ _ => True where
  getElem m k _ := m[k]?

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
Returns true if the element `a` is in the map.
```
def hashMap := ofList [("one", 1), ("two", 2)]
hashMap.contains "one" = true
hashMap.contains "three" = false
```
-/
@[inline] def contains (self : HashMap α β) (a : α) : Bool := Std.HashMap.contains self a

/--
Folds a monadic function over the elements in the map (in arbitrary order).
```
def sumEven (sum: Nat) (k : String) (v : Nat) : Except String Nat :=
  if v % 2 == 0 then pure (sum + v) else throw s!"value {v} at key {k} is not even"

foldM sumEven 0 (ofList [("one", 1), ("three", 3)]) =
  Except.error "value 3 at key three is not even"
foldM sumEven 0 (ofList [("two", 2), ("four", 4)]) = Except.ok 6
```
-/
@[inline] def foldM [Monad m] (f : δ → α → β → m δ) (init : δ) (self : HashMap α β) : m δ :=
  Std.HashMap.foldM f init self

/--
Folds a function over the elements in the map (in arbitrary order).
```
fold (fun sum _ v => sum + v) 0 (ofList [("one", 1), ("two", 2)]) = 3
```
-/
@[inline] def fold (f : δ → α → β → δ) (init : δ) (self : HashMap α β) : δ :=
  Std.HashMap.fold f init self
/--
Combines two hashmaps using a monadic function `f` to combine two values at a key.
```
def map1 := ofList [("one", 1), ("two", 2)]
def map2 := ofList [("two", 2), ("three", 3)]
def map3 := ofList [("two", 3), ("three", 3)]
def mergeIfNoConflict? (_ : String) (v₁ v₂ : Nat) : Option Nat :=
  if v₁ != v₂ then none else some v₁


mergeWithM mergeIfNoConflict? map1 map2 = some {"one" => 1, "two" => 2, "three" => 3}
mergeWithM mergeIfNoConflict? map1 map3 = none
```
-/
@[specialize] def mergeWithM [Monad m] (f : α → β → β → m β)
    (self other : HashMap α β) : m (HashMap α β) :=
  other.foldM (init := self) fun m k v₂ =>
    match m[k]? with
    | none => return m.insert k v₂
    | some v₁ => return m.insert k (← f k v₁ v₂)

/--
Combines two hashmaps using function `f` to combine two values at a key.
```
mergeWith (fun _ v₁ v₂ => v₁ + v₂ )
  (ofList [("one", 1), ("two", 2)]) (ofList [("two", 2), ("three", 3)]) =
    {"one" => 1, "two" => 4, "three" => 3}
```
-/
@[inline] def mergeWith (f : α → β → β → β) (self other : HashMap α β) : HashMap α β :=
  -- Implementing this function directly, rather than via `mergeWithM`, gives
  -- us less constrained universes.
  other.fold (init := self) fun map k v₂ =>
    match map[k]? with
    | none => map.insert k v₂
    | some v₁ => map.insert k $ f k v₁ v₂

/--
Runs a monadic function over the elements in the map (in arbitrary order).
```
def checkEven (k : String) (v : Nat) : Except String Unit :=
  if v % 2 == 0 then pure () else throw s!"value {v} at key {k} is not even"

forM checkEven (ofList [("one", 1), ("three", 3)]) = Except.error "value 3 at key three is not even"
forM checkEven (ofList [("two", 2), ("four", 4)]) = Except.ok ()
```
-/
@[inline] def forM [Monad m] (f : α → β → m PUnit) (self : HashMap α β) : m PUnit :=
  Std.HashMap.forM f self

/--
Converts the map into a list of key-value pairs.
```
open List
(ofList [("one", 1), ("two", 2)]).toList ~ [("one", 1), ("two", 2)]
```
-/
def toList (self : HashMap α β) : List (α × β) := self.fold (init := []) fun r k v => (k, v)::r

/--
Converts the map into an array of key-value pairs.
```
open List
(ofList [("one", 1), ("two", 2)]).toArray.data ~ #[("one", 1), ("two", 2)].data
```
-/
def toArray (self : HashMap α β) : Array (α × β) :=
  self.fold (init := #[]) fun r k v => r.push (k, v)

/-- The number of buckets in the hash map. -/
def numBuckets (self : HashMap α β) : Nat := Std.HashMap.Internal.numBuckets self

/--
Builds a `HashMap` from a list of key-value pairs.
Values of duplicated keys are replaced by their respective last occurrences.
```
ofList [("one", 1), ("one", 2)] = {"one" => 2}
```
-/
def ofList [BEq α] [Hashable α] (l : List (α × β)) : HashMap α β :=
  l.foldl (init := HashMap.empty) fun m (k, v) => m.insert k v

/--
Variant of `ofList` which accepts a function that combines values of duplicated keys.
```
ofListWith [("one", 1), ("one", 2)] (fun v₁ v₂ => v₁ + v₂) = {"one" => 3}
```
-/
def ofListWith [BEq α] [Hashable α] (l : List (α × β)) (f : β → β → β) : HashMap α β :=
  l.foldl (init := HashMap.empty) fun m p =>
    match m.find? p.1 with
    | none   => m.insert p.1 p.2
    | some v => m.insert p.1 <| f v p.2

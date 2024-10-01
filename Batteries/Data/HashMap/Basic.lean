/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Mario Carneiro
-/
import Batteries.Data.AssocList
import Batteries.Data.Nat.Basic
import Batteries.Data.Array.Monadic

namespace Batteries.HashMap

/-- A hash is lawful if elements which compare equal under `==` have equal hash. -/
class LawfulHashable (α : Type _) [BEq α] [Hashable α] : Prop where
  /-- Two elements which compare equal under the `BEq` instance have equal hash. -/
  hash_eq {a b : α} : a == b → hash a = hash b

namespace Imp

/--
The bucket array of a `HashMap` is a nonempty array of `AssocList`s.
(This type is an internal implementation detail of `HashMap`.)
-/
def Buckets (α : Type u) (β : Type v) := {b : Array (AssocList α β) // 0 < b.size}

namespace Buckets

/-- Construct a new empty bucket array with the specified capacity. -/
def mk (buckets := 8) (h : 0 < buckets := by decide) : Buckets α β :=
  ⟨mkArray buckets .nil, by simp [h]⟩

/-- Update one bucket in the bucket array with a new value. -/
def update (data : Buckets α β) (i : USize)
    (d : AssocList α β) (h : i.toNat < data.1.size) : Buckets α β :=
  ⟨data.1.uset i d h, (Array.size_uset ..).symm ▸ data.2⟩

/--
The number of elements in the bucket array.
Note: this is marked `noncomputable` because it is only intended for specification.
-/
noncomputable def size (data : Buckets α β) : Nat := .sum (data.1.data.map (·.toList.length))

@[simp] theorem update_size (self : Buckets α β) (i d h) :
    (self.update i d h).1.size = self.1.size := Array.size_uset ..

/-- Map a function over the values in the map. -/
@[specialize] def mapVal (f : α → β → γ) (self : Buckets α β) : Buckets α γ :=
  ⟨self.1.map (.mapVal f), by simp [self.2]⟩

/--
The well-formedness invariant for the bucket array says that every element hashes to its index
(assuming the hash is lawful - otherwise there are no promises about where elements are located).
-/
structure WF [BEq α] [Hashable α] (buckets : Buckets α β) : Prop where
  /-- The elements of a bucket are all distinct according to the `BEq` relation. -/
  distinct [LawfulHashable α] [PartialEquivBEq α] : ∀ bucket ∈ buckets.1.data,
    bucket.toList.Pairwise fun a b => ¬(a.1 == b.1)
  /-- Every element in a bucket should hash to its location. -/
  hash_self (i : Nat) (h : i < buckets.1.size) :
    buckets.1[i].All fun k _ => ((hash k).toUSize % buckets.1.size).toNat = i

end Buckets
end Imp

/-- `HashMap.Imp α β` is the internal implementation type of `HashMap α β`. -/
structure Imp (α : Type u) (β : Type v) where
  /-- The number of elements stored in the `HashMap`.
  We cache this both so that we can implement `.size` in `O(1)`, and also because we
  use the size to determine when to resize the map. -/
  size    : Nat
  /-- The bucket array of the `HashMap`. -/
  buckets : Imp.Buckets α β

namespace Imp

/--
Given a desired capacity, this returns the number of buckets we should reserve.
A "load factor" of 0.75 is the usual standard for hash maps, so we return `capacity * 4 / 3`.
-/
@[inline] def numBucketsForCapacity (capacity : Nat) : Nat :=
  capacity * 4 / 3

/-- Constructs an empty hash map with the specified nonzero number of buckets. -/
@[inline] def empty' (buckets := 8) (h : 0 < buckets := by decide) : Imp α β :=
  ⟨0, .mk buckets h⟩

/-- Constructs an empty hash map with the specified target capacity. -/
def empty (capacity := 0) : Imp α β :=
  let nbuckets := numBucketsForCapacity capacity
  let n : {n : Nat // 0 < n} :=
    if h : nbuckets = 0 then ⟨8, by decide⟩
    else ⟨nbuckets, Nat.zero_lt_of_ne_zero h⟩
  empty' n n.2

/-- Calculates the bucket index from a hash value `u`. -/
def mkIdx {n : Nat} (h : 0 < n) (u : USize) : {u : USize // u.toNat < n} :=
  ⟨u % n, USize.modn_lt _ h⟩

/--
Inserts a key-value pair into the bucket array. This function assumes that the data is not
already in the array, which is appropriate when reinserting elements into the array after a resize.
-/
@[inline] def reinsertAux [Hashable α]
    (data : Buckets α β) (a : α) (b : β) : Buckets α β :=
  let ⟨i, h⟩ := mkIdx data.2 (hash a |>.toUSize)
  data.update i (.cons a b data.1[i]) h

/-- Folds a monadic function over the elements in the map (in arbitrary order). -/
@[inline] def foldM [Monad m] (f : δ → α → β → m δ) (d : δ) (map : Imp α β) : m δ :=
  map.buckets.1.foldlM (init := d) fun d b => b.foldlM f d

/-- Folds a function over the elements in the map (in arbitrary order). -/
@[inline] def fold (f : δ → α → β → δ) (d : δ) (m : Imp α β) : δ :=
  Id.run $ foldM f d m

/-- Runs a monadic function over the elements in the map (in arbitrary order). -/
@[inline] def forM [Monad m] (f : α → β → m PUnit) (h : Imp α β) : m PUnit :=
  h.buckets.1.forM fun b => b.forM f

/-- Given a key `a`, returns a key-value pair in the map whose key compares equal to `a`. -/
def findEntry? [BEq α] [Hashable α] (m : Imp α β) (a : α) : Option (α × β) :=
  let ⟨_, buckets⟩ := m
  let ⟨i, h⟩ := mkIdx buckets.2 (hash a |>.toUSize)
  buckets.1[i].findEntry? a

/-- Looks up an element in the map with key `a`. -/
def find? [BEq α] [Hashable α] (m : Imp α β) (a : α) : Option β :=
  let ⟨_, buckets⟩ := m
  let ⟨i, h⟩ := mkIdx buckets.2 (hash a |>.toUSize)
  buckets.1[i].find? a

/-- Returns true if the element `a` is in the map. -/
def contains [BEq α] [Hashable α] (m : Imp α β) (a : α) : Bool :=
  let ⟨_, buckets⟩ := m
  let ⟨i, h⟩ := mkIdx buckets.2 (hash a |>.toUSize)
  buckets.1[i].contains a

/-- Copies all the entries from `buckets` into a new hash map with a larger capacity. -/
def expand [Hashable α] (size : Nat) (buckets : Buckets α β) : Imp α β :=
  let nbuckets := buckets.1.size * 2
  { size, buckets := go 0 buckets.1 (.mk nbuckets (Nat.mul_pos buckets.2 (by decide))) }
where
  /-- Inner loop of `expand`. Copies elements `source[i:]` into `target`,
  destroying `source` in the process. -/
  go (i : Nat) (source : Array (AssocList α β)) (target : Buckets α β) : Buckets α β :=
    if h : i < source.size then
      let idx : Fin source.size := ⟨i, h⟩
      let es := source.get idx
      -- We remove `es` from `source` to make sure we can reuse its memory cells
      -- when performing es.foldl
      let source := source.set idx .nil
      let target := es.foldl reinsertAux target
      go (i+1) source target
    else target
  termination_by source.size - i

/--
Inserts key-value pair `a, b` into the map.
If an element equal to `a` is already in the map, it is replaced by `b`.
-/
@[inline] def insert [BEq α] [Hashable α] (m : Imp α β) (a : α) (b : β) : Imp α β :=
  let ⟨size, buckets⟩ := m
  let ⟨i, h⟩ := mkIdx buckets.2 (hash a |>.toUSize)
  let bkt := buckets.1[i]
  bif bkt.contains a then
    ⟨size, buckets.update i (bkt.replace a b) h⟩
  else
    let size' := size + 1
    let buckets' := buckets.update i (.cons a b bkt) h
    if numBucketsForCapacity size' ≤ buckets.1.size then
      { size := size', buckets := buckets' }
    else
      expand size' buckets'

/--
Removes key `a` from the map. If it does not exist in the map, the map is returned unchanged.
-/
def erase [BEq α] [Hashable α] (m : Imp α β) (a : α) : Imp α β :=
  let ⟨size, buckets⟩ := m
  let ⟨i, h⟩ := mkIdx buckets.2 (hash a |>.toUSize)
  let bkt := buckets.1[i]
  bif bkt.contains a then ⟨size - 1, buckets.update i (bkt.erase a) h⟩ else ⟨size, buckets⟩

/-- Map a function over the values in the map. -/
@[inline] def mapVal (f : α → β → γ) (self : Imp α β) : Imp α γ :=
  { size := self.size, buckets := self.buckets.mapVal f }

/-- Performs an in-place edit of the value, ensuring that the value is used linearly. -/
def modify [BEq α] [Hashable α] (m : Imp α β) (a : α) (f : α → β → β) : Imp α β :=
  let ⟨size, buckets⟩ := m
  let ⟨i, h⟩ := mkIdx buckets.2 (hash a |>.toUSize)
  let bkt := buckets.1[i]
  let buckets := buckets.update i .nil h -- for linearity
  ⟨size, buckets.update i (bkt.modify a f) ((Buckets.update_size ..).symm ▸ h)⟩

/--
Applies `f` to each key-value pair `a, b` in the map. If it returns `some c` then
`a, c` is pushed into the new map; else the key is removed from the map.
-/
@[specialize] def filterMap {α : Type u} {β : Type v} {γ : Type w}
    (f : α → β → Option γ) (m : Imp α β) : Imp α γ :=
  let m' := m.buckets.1.mapM (m := StateT (ULift Nat) Id) (go .nil) |>.run ⟨0⟩ |>.run
  have : m'.1.size > 0 := by
    have := Array.size_mapM (m := StateT (ULift Nat) Id) (go .nil) m.buckets.1
    simp [SatisfiesM_StateT_eq, SatisfiesM_Id_eq] at this
    simp [this, Id.run, StateT.run, m.2.2, m']
  ⟨m'.2.1, m'.1, this⟩
where
  /-- Inner loop of `filterMap`. Note that this reverses the bucket lists,
  but this is fine since bucket lists are unordered. -/
  @[specialize] go (acc : AssocList α γ) : AssocList α β → ULift Nat → AssocList α γ × ULift Nat
  | .nil, n => (acc, n)
  | .cons a b l, n => match f a b with
    | none => go acc l n
    | some c => go (.cons a c acc) l ⟨n.1 + 1⟩

/-- Constructs a map with the set of all pairs `a, b` such that `f` returns true. -/
@[inline] def filter (f : α → β → Bool) (m : Imp α β) : Imp α β :=
  m.filterMap fun a b => bif f a b then some b else none

/--
The well-formedness invariant for a hash map. The first constructor is the real invariant,
and the others allow us to "cheat" in this file and define `insert` and `erase`,
which have more complex proofs that are delayed to `Batteries.Data.HashMap.Lemmas`.
-/
inductive WF [BEq α] [Hashable α] : Imp α β → Prop where
  /-- The real well-formedness invariant:
  * The `size` field should match the actual number of elements in the map
  * The bucket array should be well-formed, meaning that if the hashable instance
    is lawful then every element hashes to its index. -/
  | mk : m.size = m.buckets.size → m.buckets.WF → WF m
  /-- The empty hash map is well formed. -/
  | empty' : WF (empty' n h)
  /-- Inserting into a well formed hash map yields a well formed hash map. -/
  | insert : WF m → WF (insert m a b)
  /-- Removing an element from a well formed hash map yields a well formed hash map. -/
  | erase : WF m → WF (erase m a)
  /-- Replacing an element in a well formed hash map yields a well formed hash map. -/
  | modify : WF m → WF (modify m a f)

theorem WF.empty [BEq α] [Hashable α] : WF (empty n : Imp α β) := by unfold empty; apply empty'

end Imp

/--
`HashMap α β` is a key-value map which stores elements in an array using a hash function
to find the values. This allows it to have very good performance for lookups
(average `O(1)` for a perfectly random hash function), but it is not a persistent data structure,
meaning that one should take care to use the map linearly when performing updates.
Copies are `O(n)`.
-/
def _root_.Batteries.HashMap (α : Type u) (β : Type v) [BEq α] [Hashable α] := {m : Imp α β // m.WF}

open HashMap.Imp

/-- Make a new hash map with the specified capacity. -/
@[inline] def _root_.Batteries.mkHashMap [BEq α] [Hashable α] (capacity := 0) : HashMap α β :=
  ⟨.empty capacity, .empty⟩

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
@[inline] def size (self : HashMap α β) : Nat := self.1.size

/--
Is the map empty?
```
(empty : Batteries.HashMap Int Int).isEmpty = true
(ofList [("one", 1), ("two", 2)]).isEmpty = false
```
-/
@[inline] def isEmpty (self : HashMap α β) : Bool := self.size = 0

/--
Inserts key-value pair `a, b` into the map.
If an element equal to `a` is already in the map, it is replaced by `b`.
```
def hashMap := ofList [("one", 1), ("two", 2)]
hashMap.insert "three" 3 = {"one" => 1, "two" => 2, "three" => 3}
hashMap.insert "two" 0 = {"one" => 1, "two" => 0}
```
-/
def insert (self : HashMap α β) (a : α) (b : β) : HashMap α β := ⟨self.1.insert a b, self.2.insert⟩

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
  let old := m.size
  let m' := m.insert a b
  let replaced := old == m'.size
  (m', replaced)

/--
Removes key `a` from the map. If it does not exist in the map, the map is returned unchanged.
```
def hashMap := ofList [("one", 1), ("two", 2)]
hashMap.erase "one" = {"two" => 2}
hashMap.erase "three" = {"one" => 1, "two" => 2}
```
-/
@[inline] def erase (self : HashMap α β) (a : α) : HashMap α β := ⟨self.1.erase a, self.2.erase⟩

/--
Performs an in-place edit of the value, ensuring that the value is used linearly.
The function `f` is passed the original key of the entry, along with the value in the map.
```
(ofList [("one", 1), ("two", 2)]).modify "one" (fun _ v => v + 1) = {"one" => 2, "two" => 2}
(ofList [("one", 1), ("two", 2)]).modify "three" (fun _ v => v + 1) = {"one" => 1, "two" => 2}
```
-/
def modify (self : HashMap α β) (a : α) (f : α → β → β) : HashMap α β :=
  ⟨self.1.modify a f, self.2.modify⟩

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
@[inline] def findEntry? (self : HashMap α β) (a : α) : Option (α × β) := self.1.findEntry? a

/--
Looks up an element in the map with key `a`.
```
def hashMap := ofList [("one", 1), ("two", 2)]
hashMap.find? "one" = some 1
hashMap.find? "three" = none
```
-/
@[inline] def find? (self : HashMap α β) (a : α) : Option β := self.1.find? a

/--
Looks up an element in the map with key `a`. Returns `b₀` if the element is not found.
```
def hashMap := ofList [("one", 1), ("two", 2)]
hashMap.findD "one" 0 = 1
hashMap.findD "three" 0 = 0
```
-/
@[inline] def findD (self : HashMap α β) (a : α) (b₀ : β) : β := (self.find? a).getD b₀

/--
Looks up an element in the map with key `a`. Panics if the element is not found.
```
def hashMap := ofList [("one", 1), ("two", 2)]
hashMap.find! "one" = 1
hashMap.find! "three" => panic!
```
-/
@[inline] def find! [Inhabited β] (self : HashMap α β) (a : α) : β :=
  (self.find? a).getD (panic! "key is not in the map")

instance : GetElem (HashMap α β) α (Option β) fun _ _ => True where
  getElem m k _ := m.find? k

/--
Returns true if the element `a` is in the map.
```
def hashMap := ofList [("one", 1), ("two", 2)]
hashMap.contains "one" = true
hashMap.contains "three" = false
```
-/
@[inline] def contains (self : HashMap α β) (a : α) : Bool := self.1.contains a

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
  self.1.foldM f init

/--
Folds a function over the elements in the map (in arbitrary order).
```
fold (fun sum _ v => sum + v) 0 (ofList [("one", 1), ("two", 2)]) = 3
```
-/
@[inline] def fold (f : δ → α → β → δ) (init : δ) (self : HashMap α β) : δ := self.1.fold f init

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
    match m.find? k with
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
    match map.find? k with
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
@[inline] def forM [Monad m] (f : α → β → m PUnit) (self : HashMap α β) : m PUnit := self.1.forM f

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
def numBuckets (self : HashMap α β) : Nat := self.1.buckets.1.size

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

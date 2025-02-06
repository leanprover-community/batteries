/-
Copyright (c) 2023 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Lean.Data.NameMap


namespace Lean.NameSet

instance : Singleton Name NameSet where
  singleton := fun n => (∅ : NameSet).insert n

instance : Union NameSet where
  union := fun s t => s.fold (fun t n => t.insert n) t

instance : Inter NameSet where
  inter := fun s t => s.fold (fun r n => if t.contains n then r.insert n else r) {}

instance : SDiff NameSet where
  sdiff := fun s t => t.fold (fun s n => s.erase n) s

/-- Create a `Lean.NameSet` from a `List`. This operation is `O(n)` in the length of the list. -/
def ofList (l : List Name) : NameSet :=
  l.foldl (fun s n => s.insert n) {}

/-- Create a `Lean.NameSet` from an `Array`. This operation is `O(n)` in the size of the array. -/
def ofArray (a : Array Name) : NameSet :=
  a.foldl (fun s n => s.insert n) {}

end Lean.NameSet

/-
Copyright (c) 2024 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

import Batteries.Data.Vector.Basic
import Init.Data.Array.Basic
import Init.Data.Array.Lemmas
import Batteries.Classes.SatisfiesM

/-!
## Monadic Definitions for Vectors
In this file we add monadic definitions for statically sized vectors.
-/

namespace Batteries

namespace Vector

/--
`modifyM v i f` applies a monadic transformation `f` to `v[i]`
-/
def modifyM [Monad m] (v : Vector α n) (i : Nat)
  (f : α → m α) : m (Vector α n) := do
    return ⟨←Array.modifyM v.toArray i f,
      by rw[←v.size_eq]; sorry⟩

/--
`modify v i f` takes a vector `v`, index `i`, and a modification function `f`
and sets `v[i]` to `f`.
-/
@[inline]
def modify (v : Vector α n) (i : Nat) (f : α → α) : Vector α n :=
  Id.run <| modifyM v i f

/--
`forIn v acc f` iterates over `v` applying `f` on each element and the
accumulated result. The final value of `acc` after the completion of the loop
is returned.
-/
protected def forIn {α : Type u} {β : Type v} {m : Type v → Type w} [Monad m]
  (v : Vector α n) (acc : β) (f : α → β → m (ForInStep β)) : m β := do
    Array.forIn v.toArray acc f

instance : ForIn m (Vector α n) α where
  forIn := Vector.forIn

/--
`foldlM f init v start stop` is the monadic left fold function that folds `f`
over `v` from left to right.
-/
def foldlM {α : Type u} {β : Type v} {m : Type v → Type w} [Monad m]
  (f : β → α → m β) (init : β)
  (v : Vector α n) (start := 0) (stop := n) : m β := do
    Array.foldlM f init v.toArray start stop

/--
`foldrM f init v start stop` is the monadic right fold function that folds `f`
over `v` from right to left.
-/
def foldrM {α : Type u} {β : Type v} {m : Type v → Type w} [Monad m]
  (f : α → β → m β) (init : β) (v : Vector α n)
  (start := n) (stop := 0) : m β :=
    Array.foldrM f init v.toArray start stop

/--
`mapM f v` maps a monadic function `f : α → m β` over `v` and returns
the resultant vector in the same monad `m`.
-/
def mapM {α : Type u} {β : Type v} {m : Type v → Type w} [Monad m]
  (f : α → m β) (v : Vector α n) : m (Vector β n) := do
    return ⟨←Array.mapM f v.toArray, by rw[←v.size_eq]; sorry⟩

/--
`mapIdx f v` maps a monadic function `f : Fin n → α → m β` that takes vector
elements and their index, and maps them over `v`. It returns the resultant
vector in the same monad `m`.
-/
@[inline]
def mapIdxM {α : Type u} {β : Type v} {m : Type v → Type w} [Monad m]
  (v : Vector α n) (f : Fin n → α → m β) : m (Vector β n) := do
    return ⟨←Array.mapIdxM v.toArray (v.size_eq.symm ▸ f),
      by rw[←v.size_eq]; sorry⟩

@[inline]
def findSomeM? {α : Type u} {β : Type v} {m : Type v → Type w} [Monad m]
  (v : Vector α n) (f : α → m (Option β)) : m (Option β) :=
    Array.findSomeM? v.toArray f

@[inline]
def findM? {α : Type} {m : Type → Type} [Monad m]
  (v : Vector α n) (p : α → m Bool) : m (Option α) := do
    Array.findM? v.toArray p

@[inline]
def findIdxM? [Monad m] (v : Vector α n) (p : α → m Bool) : m (Option Nat) := do
    Array.findIdxM? v.toArray p


def anyM {α : Type u} {m : Type → Type w} [Monad m] (p : α → m Bool)
  (v : Vector α n) (start := 0) (stop := n) : m Bool :=
    Array.anyM p v.toArray start stop

@[inline]
def allM {α : Type u} {m : Type → Type w} [Monad m] (p : α → m Bool)
  (v : Vector α n) (start := 0) (stop := n) : m Bool :=
    Array.allM p v.toArray start stop

@[inline]
def findSomeRevM? {α : Type u} {β : Type v} {m : Type v → Type w} [Monad m]
  (v : Vector α n) (f : α → m (Option β)) : m (Option β) :=
    Array.findSomeRevM? v.toArray f

@[inline]
def findRevM? {α : Type} {m : Type → Type w} [Monad m] (v : Vector α n)
  (p : α → m Bool) : m (Option α) := Array.findRevM? v.toArray p

@[inline]
def forM {α : Type u} {m : Type v → Type w} [Monad m] (f : α → m PUnit)
  (as : Array α) (start := 0) (stop := as.size) : m PUnit :=
  as.foldlM (fun _ => f) ⟨⟩ start stop

@[inline]
def forRevM {α : Type u} {m : Type v → Type w} [Monad m] (f : α → m PUnit)
  (v : Vector α n) (start := n) (stop := 0) : m PUnit :=
  v.toArray.foldrM (fun a _ => f a) ⟨⟩ start stop

@[inline]
def foldl {α : Type u} {β : Type v} (f : β → α → β) (init : β)
  (v : Vector α n) (start := 0) (stop := n) : β :=
    Id.run <| v.foldlM f init start stop

@[inline]
def foldr {α : Type u} {β : Type v} (f : α → β → β) (init : β)
  (v : Vector α n) (start := n) (stop := 0) : β :=
    Id.run <| v.foldrM f init start stop

@[inline]
def mapIdx {α : Type u} {β : Type v} (v : Vector α n)
  (f : Fin n → α → β) : Vector β n :=
    Id.run <| v.mapIdxM f

/-- Turns `#[a, b]` into `#[(a, 0), (b, 1)]`. -/
def zipWithIndex (v : Vector α n) : Vector (α × Nat) n :=
  v.mapIdx fun i a => (a, i)

@[inline]
def find? {α : Type} (v : Vector α n) (p : α → Bool) : Option α :=
  Id.run <| v.findM? p

@[inline]
def findSome? {α : Type u} {β : Type v} (v : Vector α n)
  (f : α → Option β) : Option β :=
    Id.run <| v.findSomeM? f

@[inline]
def findSome! {α : Type u} {β : Type v} [Inhabited β] (v : Vector α n)
  (f : α → Option β) : β := Array.findSome! v.toArray f

@[inline]
def findSomeRev? {α : Type u} {β : Type v} (v : Vector α n) (f : α → Option β)
  : Option β :=
    Id.run <| v.findSomeRevM? f

@[inline]
def findRev? {α : Type} (v : Vector α n) (p : α → Bool) : Option α :=
  Id.run <| v.findRevM? p

/--
Check whether vectors `xs` and `ys` are equal as sets, i.e. they
contain the same elements when disregarding order and duplicates.
-/
def equalSet [BEq α] (xs ys : Vector α n) : Bool :=
  xs.toArray.all (ys.toArray.contains ·)
    && ys.toArray.all (xs.toArray.contains ·)

set_option linter.unusedVariables.funArgs false in
/--
Returns the first minimal element among `d` and elements of the vector.
If `start` and `stop` are given, only the subarray `xs[start:stop]` is
considered (in addition to `d`).
-/
@[inline]
protected def minWith [ord : Ord α]
    (xs : Vector α n) (d : α) (start := 0) (stop := n) : α :=
  xs.foldl (init := d) (start := start) (stop := stop) fun min x =>
    if compare x min |>.isLT then x else min

set_option linter.unusedVariables.funArgs false in
/--
Find the first minimal element of a vector. If the array is empty, `d` is
returned. If `start` and `stop` are given, only the subarray `xs[start:stop]` is
considered.
-/
@[inline]
protected def minD [ord : Ord α]
    (xs : Vector α n) (d : α) (start := 0) (stop := xs.size) : α :=
  if h: start < xs.size ∧ start < stop then
    xs.minWith (xs.get ⟨start, h.left⟩) (start + 1) stop
  else
    d

set_option linter.unusedVariables.funArgs false in
/--
Find the first minimal element of a vector. If the vector is empty, `none` is
returned. If `start` and `stop` are given, only the subarray `xs[start:stop]` is
considered.
-/
@[inline]
protected def min? [ord : Ord α]
    (xs : Vector α n) (start := 0) (stop := xs.size) : Option α :=
  if h : start < xs.size ∧ start < stop then
    some $ xs.minD (xs.get ⟨start, h.left⟩) start stop
  else
    none

set_option linter.unusedVariables.funArgs false in
/--
Find the first minimal element of a vector. If the vector is empty, `default` is
returned. If `start` and `stop` are given, only the subvector `xs[start:stop]`
is considered.
-/
@[inline]
protected def minI [ord : Ord α] [Inhabited α]
    (xs : Vector α n) (start := 0) (stop := xs.size) : α :=
  xs.minD default start stop

set_option linter.unusedVariables.funArgs false in
/--
Returns the first maximal element among `d` and elements of the vector.
If `start` and `stop` are given, only the subvector `xs[start:stop]` is
considered (in addition to `d`).
-/
@[inline]
protected def maxWith [ord : Ord α]
    (xs : Vector α n) (d : α) (start := 0) (stop := xs.size) : α :=
  xs.minWith (ord := ord.opposite) d start stop

set_option linter.unusedVariables.funArgs false in
/--
Find the first maximal element of a vector. If the vector is empty, `d` is
returned. If `start` and `stop` are given, only the subvector `xs[start:stop]`
is considered.
-/
@[inline]
protected def maxD [ord : Ord α]
    (xs : Vector α n) (d : α) (start := 0) (stop := xs.size) : α :=
  xs.minD (ord := ord.opposite) d start stop

set_option linter.unusedVariables.funArgs false in
/--
Find the first maximal element of a vector. If the vector is empty, `none` is
returned. If `start` and `stop` are given, only the subvector `xs[start:stop]`
is considered.
-/
@[inline]
protected def max? [ord : Ord α]
    (xs : Vector α n) (start := 0) (stop := xs.size) : Option α :=
  xs.min? (ord := ord.opposite) start stop

set_option linter.unusedVariables.funArgs false in
/--
Find the first maximal element of a vector. If the vector is empty, `default` is
returned. If `start` and `stop` are given, only the subvector `xs[start:stop]`
is considered.
-/
@[inline]
protected def maxI [ord : Ord α] [Inhabited α]
    (xs : Array α) (start := 0) (stop := xs.size) : α :=
  xs.minI (ord := ord.opposite) start stop

end Vector
end Batteries

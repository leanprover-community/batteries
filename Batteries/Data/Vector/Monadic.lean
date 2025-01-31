/-
Copyright (c) 2024 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

import Init.Data.Vector
import Init.Data.Array.Basic
import Init.Data.Array.Lemmas
import Batteries.Data.Array.Monadic
import Batteries.Classes.SatisfiesM

/-!
## Monadic Definitions for Vectors
In this file we add some monadic definitions for statically sized vectors.
-/

namespace Batteries

namespace Vector

/--
`modifyM v i f` applies a monadic transformation `f` to `v[i]`
-/
def modifyM [Monad m] (v : Vector α n) (i : Nat)
  (f : α → m α) : m (Vector α n) := do
    return ⟨←Array.modifyM v.toArray i f,
      by rw[Array.size_modifyM]⟩

/--
`modify v i f` takes a vector `v`, index `i`, and a modification function `f`
and sets `v[i]` to `f`.
-/
@[inline]
def modify (v : Vector α n) (i : Nat) (f : α → α) : Vector α n :=
  Id.run <| modifyM v i f

@[inline]
def findSomeM? {α : Type u} {β : Type v} {m : Type v → Type w} [Monad m]
  (v : Vector α n) (f : α → m (Option β)) : m (Option β) :=
    Array.findSomeM? f v.toArray

@[inline]
def findM? {α : Type} {m : Type → Type} [Monad m]
  (v : Vector α n) (p : α → m Bool) : m (Option α) := do
    Array.findM? p v.toArray

@[inline]
def findIdxM? [Monad m] (v : Vector α n) (p : α → m Bool) : m (Option Nat) := do
    Array.findIdxM? p v.toArray


@[inline]
def findSomeRevM? {α : Type u} {β : Type v} {m : Type v → Type w} [Monad m]
  (v : Vector α n) (f : α → m (Option β)) : m (Option β) :=
    Array.findSomeRevM? f v.toArray

@[inline]
def findRevM? {α : Type} {m : Type → Type w} [Monad m] (v : Vector α n)
  (p : α → m Bool) : m (Option α) := Array.findRevM? p v.toArray

@[inline]
def forRevM {α : Type u} {m : Type v → Type w} [Monad m] (f : α → m PUnit)
  (v : Vector α n) (start := n) (stop := 0) : m PUnit :=
  v.toArray.foldrM (fun a _ => f a) ⟨⟩ start stop


@[inline]
def findSomeRev? {α : Type u} {β : Type v} (v : Vector α n) (f : α → Option β)
  : Option β :=
    Id.run <| v.findSomeRevM? f

@[inline]
def findRev? {α : Type} (v : Vector α n) (p : α → Bool) : Option α :=
  Id.run <| v.findRevM? p





end Vector
end Batteries

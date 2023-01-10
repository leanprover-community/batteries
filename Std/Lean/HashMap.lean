/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Lean.Data.HashMap

namespace Lean.HashMap

variable [BEq α] [Hashable α]

instance : ForIn m (HashMap α β) (α × β) where
  forIn m init f := do
    let mut acc := init
    for buckets in m.val.buckets.val do
      for d in buckets do
        match ← f d acc with
        | .done b => return b
        | .yield b => acc := b
    return acc

/--
`O(|other|)` amortized. Merge two `HashMap`s.
The values of keys which appear in both maps are combined using the monadic function `f`.
-/
@[specialize]
def mergeWithM {m α β} [BEq α] [Hashable α] [Monad m] (f : α → β → β → m β)
    (self other : HashMap α β) : m (HashMap α β) :=
  other.foldM (init := self) fun map k v₂ =>
    match map.find? k with
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
    match map.find? k with
    | none => map.insert k v₂
    | some v₁ => map.insert k <| f k v₁ v₂

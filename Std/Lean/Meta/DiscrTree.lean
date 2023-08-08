/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg, Scott Morrison
-/

import Lean.Meta.DiscrTree
import Std.Data.Array.Merge
import Std.Data.Ord
import Std.Lean.Meta.Expr
import Std.Lean.PersistentHashMap

namespace Lean.Meta.DiscrTree

namespace Key

/--
Compare two `Key`s. The ordering is total but otherwise arbitrary. (It uses
`Name.quickCmp` internally.)
-/
protected def cmp : Key s → Key s → Ordering
  | .lit v₁,        .lit v₂        => compare v₁ v₂
  | .fvar n₁ a₁,    .fvar n₂ a₂    => n₁.name.quickCmp n₂.name |>.then <| compare a₁ a₂
  | .const n₁ a₁,   .const n₂ a₂   => n₁.quickCmp n₂ |>.then <| compare a₁ a₂
  | .proj s₁ i₁ a₁, .proj s₂ i₂ a₂ =>
    s₁.quickCmp s₂ |>.then <| compare i₁ i₂ |>.then <| compare a₁ a₂
  | k₁,             k₂             => compare k₁.ctorIdx k₂.ctorIdx

instance : Ord (Key s) :=
  ⟨Key.cmp⟩

end Key


namespace Trie

-- This is just a partial function, but Lean doesn't realise that its type is
-- inhabited.
private unsafe def foldMUnsafe [Monad m] (initialKeys : Array (Key s))
    (f : σ → Array (Key s) → α → m σ) (init : σ) : Trie α s → m σ
  | Trie.node vs children => do
    let s ← vs.foldlM (init := init) fun s v => f s initialKeys v
    children.foldlM (init := s) fun s (k, t) =>
      t.foldMUnsafe (initialKeys.push k) f s

/--
Monadically fold the keys and values stored in a `Trie`.
-/
@[implemented_by foldMUnsafe]
opaque foldM [Monad m] (initalKeys : Array (Key s))
    (f : σ → Array (Key s) → α → m σ) (init : σ) (t : Trie α s) : m σ :=
  pure init

/--
Fold the keys and values stored in a `Trie`.
-/
@[inline]
def fold (initialKeys : Array (Key s)) (f : σ → Array (Key s) → α → σ)
    (init : σ) (t : Trie α s) : σ :=
  Id.run <| t.foldM initialKeys (init := init) fun s k a => return f s k a

-- This is just a partial function, but Lean doesn't realise that its type is
-- inhabited.
private unsafe def foldValuesMUnsafe [Monad m] (f : σ → α → m σ) (init : σ) :
    Trie α s → m σ
| node vs children => do
  let s ← vs.foldlM (init := init) f
  children.foldlM (init := s) fun s (_, c) => c.foldValuesMUnsafe (init := s) f

/--
Monadically fold the values stored in a `Trie`.
-/
@[implemented_by foldValuesMUnsafe]
opaque foldValuesM [Monad m] (f : σ → α → m σ) (init : σ) (t : Trie α s) : m σ := pure init

/--
Fold the values stored in a `Trie`.
-/
@[inline]
def foldValues (f : σ → α → σ) (init : σ) (t : Trie α s) : σ :=
  Id.run <| t.foldValuesM (init := init) f

/--
The number of values stored in a `Trie`.
-/
partial def size : Trie α s → Nat
  | Trie.node vs children =>
    children.foldl (init := vs.size) fun n (_, c) => n + size c

/--
Merge two `Trie`s. Duplicate values are preserved.
-/
partial def mergePreservingDuplicates : Trie α s → Trie α s → Trie α s
  | node vs₁ cs₁, node vs₂ cs₂ =>
    node (vs₁ ++ vs₂) (mergeChildren cs₁ cs₂)
where
  /-- Auxiliary definition for `mergePreservingDuplicates`. -/
  mergeChildren (cs₁ cs₂ : Array (Key s × Trie α s)) :
      Array (Key s × Trie α s) :=
    Array.mergeSortedMergingDuplicates
      (ord := ⟨compareOn (·.fst)⟩) cs₁ cs₂
      (fun (k₁, t₁) (_, t₂) => (k₁, mergePreservingDuplicates t₁ t₂))

end Trie


/--
Monadically fold over the keys and values stored in a `DiscrTree`.
-/
@[inline]
def foldM [Monad m] (f : σ → Array (Key s) → α → m σ) (init : σ)
    (t : DiscrTree α s) : m σ :=
  t.root.foldlM (init := init) fun s k t => t.foldM #[k] (init := s) f

/--
Fold over the keys and values stored in a `DiscrTree`
-/
@[inline]
def fold (f : σ → Array (Key s) → α → σ) (init : σ) (t : DiscrTree α s) : σ :=
  Id.run <| t.foldM (init := init) fun s keys a => return f s keys a

/--
Monadically fold over the values stored in a `DiscrTree`.
-/
@[inline]
def foldValuesM [Monad m] (f : σ → α → m σ) (init : σ) (t : DiscrTree α s) :
    m σ :=
  t.root.foldlM (init := init) fun s _ t => t.foldValuesM (init := s) f

/--
Fold over the values stored in a `DiscrTree`.
-/
@[inline]
def foldValues (f : σ → α → σ) (init : σ) (t : DiscrTree α s) : σ :=
  Id.run <| t.foldValuesM (init := init) f

/--
Extract the values stored in a `DiscrTree`.
-/
@[inline]
def values (t : DiscrTree α s) : Array α :=
  t.foldValues (init := #[]) fun as a => as.push a

/--
Extract the keys and values stored in a `DiscrTree`.
-/
@[inline]
def toArray (t : DiscrTree α s) : Array (Array (Key s) × α) :=
  t.fold (init := #[]) fun as keys a => as.push (keys, a)

/--
Get the number of values stored in a `DiscrTree`. O(n) in the size of the tree.
-/
@[inline]
def size (t : DiscrTree α s) : Nat :=
  t.root.foldl (init := 0) fun n _ t => n + t.size

/--
Merge two `DiscrTree`s. Duplicate values are preserved.
-/
@[inline]
def mergePreservingDuplicates (t u : DiscrTree α s) : DiscrTree α s :=
  ⟨t.root.mergeWith u.root fun _ trie₁ trie₂ =>
    trie₁.mergePreservingDuplicates trie₂⟩

/--
Inserts a new key into a discrimination tree,
but only if it is not of the form `#[*]` or `#[=, *, *, *]`.
-/
def insertIfSpecific [BEq α] (d : DiscrTree α s)
    (keys : Array (DiscrTree.Key s)) (v : α) : DiscrTree α s :=
  if keys == #[Key.star] || keys == #[Key.const `Eq 3, Key.star, Key.star, Key.star] then
    d
  else
    d.insertCore keys v

variable {m : Type → Type} [Monad m]

/-- Apply a monadic function to the array of values at each node in a `DiscrTree`. -/
partial def Trie.mapArraysM (t : DiscrTree.Trie α s) (f : Array α → m (Array β)) :
    m (DiscrTree.Trie β s) := do
  match t with
  | .node vs children =>
    return .node (← f vs) (← children.mapM fun (k, t') => do pure (k, ← t'.mapArraysM f))

/-- Apply a monadic function to the array of values at each node in a `DiscrTree`. -/
def mapArraysM (d : DiscrTree α s) (f : Array α → m (Array β)) : m (DiscrTree β s) := do
  pure { root := ← d.root.mapM (fun t => t.mapArraysM f) }

/-- Apply a function to the array of values at each node in a `DiscrTree`. -/
def mapArrays (d : DiscrTree α s) (f : Array α → Array β) : DiscrTree β s :=
  d.mapArraysM fun A => (pure (f A) : Id (Array β))

end Lean.Meta.DiscrTree

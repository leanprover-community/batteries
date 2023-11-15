/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg, Scott Morrison
-/

import Lean.Meta.DiscrTree
import Std.Data.Array.Merge
import Std.Data.Array.Attach
import Std.Data.Ord
import Std.Lean.Meta.Expr
import Std.Lean.PersistentHashMap

namespace Lean.Meta.DiscrTree

namespace Key

/--
Compare two `Key`s. The ordering is total but otherwise arbitrary. (It uses
`Name.quickCmp` internally.)
-/
protected def cmp : Key → Key → Ordering
  | .lit v₁,        .lit v₂        => compare v₁ v₂
  | .fvar n₁ a₁,    .fvar n₂ a₂    => n₁.name.quickCmp n₂.name |>.then <| compare a₁ a₂
  | .const n₁ a₁,   .const n₂ a₂   => n₁.quickCmp n₂ |>.then <| compare a₁ a₂
  | .proj s₁ i₁ a₁, .proj s₂ i₂ a₂ =>
    s₁.quickCmp s₂ |>.then <| compare i₁ i₂ |>.then <| compare a₁ a₂
  | k₁,             k₂             => compare k₁.ctorIdx k₂.ctorIdx

instance : Ord Key := ⟨Key.cmp⟩

end Key


namespace Trie

theorem termination_helper {cs : Array (Key × Trie α)} {k : Key} {c : Trie α} (h : (k, c) ∈ cs) :
    sizeOf c < sizeOf cs := calc
  sizeOf c < sizeOf (k, c) := by simp_arith
  _ < sizeOf cs := Array.sizeOf_lt_of_mem h

/--
A termination tactic specialized to the recursion patterns of `Trie`.
(A more compositional setup of the default decreasing tactics might make this unnecessary.)
-/
macro "decreasing_trie" : tactic =>
  `(tactic| decreasing_with first
      | decreasing_trivial
      | apply termination_helper (by assumption); done
      | apply Nat.lt_trans (termination_helper (by assumption)); simp_arith; done)

/--
Monadically fold the keys and values stored in a `Trie`.
-/
def foldM [Monad m] (initialKeys : Array Key)
    (f : σ → Array Key → α → m σ) (init : σ) : Trie α → m σ
  | Trie.node vs children => do
    let s ← vs.foldlM (init := init) fun s v => f s initialKeys v
    children.attach.foldlM (init := s) fun s ⟨(k, t), _h⟩ =>
      t.foldM (initialKeys.push k) f s
termination_by _ _ _ _ t => t
decreasing_by decreasing_trie

/--
Fold the keys and values stored in a `Trie`.
-/
@[inline]
def fold (initialKeys : Array Key) (f : σ → Array Key → α → σ)
    (init : σ) (t : Trie α) : σ :=
  Id.run <| t.foldM initialKeys (init := init) fun s k a => return f s k a

/--
Monadically fold the values stored in a `Trie`.
-/
def foldValuesM [Monad m] (f : σ → α → m σ) (init : σ) :
    Trie α → m σ
| node vs children => do
  let s ← vs.foldlM (init := init) f
  children.attach.foldlM (init := s) fun s ⟨(_, c), _⟩ => c.foldValuesM (init := s) f
decreasing_by decreasing_trie

/--
Fold the values stored in a `Trie`.
-/
@[inline]
def foldValues (f : σ → α → σ) (init : σ) (t : Trie α) : σ :=
  Id.run <| t.foldValuesM (init := init) f

/--
The number of values stored in a `Trie`.
-/
def size : Trie α → Nat
  | Trie.node vs children =>
    children.attach.foldl (init := vs.size) fun n ⟨(_, c),_ ⟩ => n + size c
decreasing_by decreasing_trie

/--
Merge two `Trie`s. Duplicate values are preserved.
-/
def mergePreservingDuplicates : Trie α → Trie α → Trie α
  | node vs₁ cs₁, node vs₂ cs₂ =>
    node (vs₁ ++ vs₂) (mergeChildren cs₁ cs₂)
where
  /-- Auxiliary definition for `mergePreservingDuplicates`. -/
  mergeChildren (cs₁ cs₂ : Array (Key × Trie α)) :
        Array (Key × Trie α) :=
      Array.mergeSortedMergingDuplicates
        (compare := fun x y => compare x.val.fst y.fst) cs₁.attach cs₂
        Subtype.val id
        (fun ⟨(k₁, t₁),_⟩ (_, t₂) => (k₁, mergePreservingDuplicates t₁ t₂))
termination_by
  mergePreservingDuplicates t _ => sizeOf t
  mergeChildren cs _ => sizeOf cs
decreasing_by decreasing_trie

end Trie


/--
Monadically fold over the keys and values stored in a `DiscrTree`.
-/
@[inline]
def foldM [Monad m] (f : σ → Array Key → α → m σ) (init : σ)
    (t : DiscrTree α) : m σ :=
  t.root.foldlM (init := init) fun s k t => t.foldM #[k] (init := s) f

/--
Fold over the keys and values stored in a `DiscrTree`
-/
@[inline]
def fold (f : σ → Array Key → α → σ) (init : σ) (t : DiscrTree α) : σ :=
  Id.run <| t.foldM (init := init) fun s keys a => return f s keys a

/--
Monadically fold over the values stored in a `DiscrTree`.
-/
@[inline]
def foldValuesM [Monad m] (f : σ → α → m σ) (init : σ) (t : DiscrTree α) :
    m σ :=
  t.root.foldlM (init := init) fun s _ t => t.foldValuesM (init := s) f

/--
Fold over the values stored in a `DiscrTree`.
-/
@[inline]
def foldValues (f : σ → α → σ) (init : σ) (t : DiscrTree α) : σ :=
  Id.run <| t.foldValuesM (init := init) f

/--
Extract the values stored in a `DiscrTree`.
-/
@[inline]
def values (t : DiscrTree α) : Array α :=
  t.foldValues (init := #[]) fun as a => as.push a

/--
Extract the keys and values stored in a `DiscrTree`.
-/
@[inline]
def toArray (t : DiscrTree α) : Array (Array Key × α) :=
  t.fold (init := #[]) fun as keys a => as.push (keys, a)

/--
Get the number of values stored in a `DiscrTree`. O(n) in the size of the tree.
-/
@[inline]
def size (t : DiscrTree α) : Nat :=
  t.root.foldl (init := 0) fun n _ t => n + t.size

/--
Merge two `DiscrTree`s. Duplicate values are preserved.
-/
@[inline]
def mergePreservingDuplicates (t u : DiscrTree α) : DiscrTree α :=
  ⟨t.root.mergeWith u.root fun _ trie₁ trie₂ =>
    trie₁.mergePreservingDuplicates trie₂⟩

/--
Inserts a new key into a discrimination tree,
but only if it is not of the form `#[*]` or `#[=, *, *, *]`.
-/
def insertIfSpecific [BEq α] (d : DiscrTree α)
    (keys : Array DiscrTree.Key) (v : α) (config : WhnfCoreConfig) : DiscrTree α :=
  if keys == #[Key.star] || keys == #[Key.const `Eq 3, Key.star, Key.star, Key.star] then
    d
  else
    d.insertCore keys v config

variable {m : Type → Type} [Monad m]

/-- Apply a monadic function to the array of values at each node in a `DiscrTree`. -/
partial def Trie.mapArraysM (t : DiscrTree.Trie α) (f : Array α → m (Array β)) :
    m (DiscrTree.Trie β) :=
  match t with
  | .node vs children =>
    return .node (← f vs) (← children.mapM fun (k, t') => do pure (k, ← t'.mapArraysM f))

/-- Apply a monadic function to the array of values at each node in a `DiscrTree`. -/
def mapArraysM (d : DiscrTree α) (f : Array α → m (Array β)) : m (DiscrTree β) := do
  pure { root := ← d.root.mapM (fun t => t.mapArraysM f) }

/-- Apply a function to the array of values at each node in a `DiscrTree`. -/
def mapArrays (d : DiscrTree α) (f : Array α → Array β) : DiscrTree β :=
  Id.run <| d.mapArraysM fun A => pure (f A)

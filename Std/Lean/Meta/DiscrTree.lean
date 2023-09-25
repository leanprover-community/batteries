/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
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
  | .empty => pure init
  | .values vs t => do
    let s ← vs.foldlM (init := init) fun s v => f s initialKeys v
    t.foldMUnsafe initialKeys f s
  | .path ks t => t.foldMUnsafe (initialKeys ++ ks) f init
  | .branch cs => do
    cs.foldlM (init := init) fun s (k, t) =>
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
  | .empty => pure init
  | .values vs t => do
    let s ← vs.foldlM (init := init) fun s v => f s v
    t.foldValuesMUnsafe f s
  | .path _ t => t.foldValuesMUnsafe f init
  | .branch cs => do
    cs.foldlM (init := init) fun s (_, t) => t.foldValuesMUnsafe f s

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
  | .empty => 0
  | .values vs t => vs.size + t.size
  | .path _ t => t.size
  | .branch cs => cs.foldl (init := 0) fun n (_, c) => n + c.size

/-- Just until Ci built the toolchain -/
opaque _root_.Lean.Meta.DiscrTree.commonPrefix (ks1 : Array (Key s)) (ks2 : Array (Key s)) (i : Nat) : Nat


/--
Merge two `Trie`s. Duplicate values are preserved.
-/
partial def mergePreservingDuplicates : Trie α s → Trie α s → Trie α s
  | .empty, t => t
  | t, .empty => t
  | .values vs₁ t₁, .values vs₂ t₂ =>
    .values (vs₁ ++ vs₂) (mergePreservingDuplicates t₁ t₂)
  | .values vs₁ t₁, t₂ =>
    .values vs₁ (mergePreservingDuplicates t₁ t₂)
  | t₁, .values vs₂ t₂ =>
    .values vs₂ (mergePreservingDuplicates t₁ t₂)

  | .branch cs₁, .branch cs₂ =>
    .branch (mergeChildren cs₁ cs₂)
  -- paths and branches are merged by converting the path to a (singleton) branch
  | .path ks t, .branch cs₂ =>
    let cs₁ := pathChildren ks t
    .branch (mergeChildren cs₁ cs₂)
  | .branch cs₁, .path ks t =>
    let cs₂ := pathChildren ks t
    .branch (mergeChildren cs₁ cs₂)
  -- two paths are merged by splitting after the common prefix
  | .path ks₁ t₁, .path ks₂ t₂ =>
    let j := Lean.Meta.DiscrTree.commonPrefix ks₁ ks₂ 0
    mkPath (ks₁.extract 0 j) $ -- the common prefix
      if h₁ : j < ks₁.size then
        if h₂ : j < ks₂.size then
          -- introduce a branch
          mkBranch2 (ks₁.get ⟨j, h₁⟩) (mkPath (ks₁.extract (j + 1) ks₁.size) t₁)
                    (ks₂.get ⟨j, h₂⟩) (mkPath (ks₂.extract (j + 1) ks₂.size) t₂)
        else
          -- ks₂ is a prefix of ks₁, split and merge
          mergePreservingDuplicates (mkPath (ks₁.extract j ks₁.size) t₁) t₂
      else
        -- ks₁ is a prefix of ks₂, split and merge
        mergePreservingDuplicates t₁ (mkPath (ks₂.extract j ks₂.size) t₂)

where
  /-- Auxiliary definition for `mergePreservingDuplicates`. -/
  mergeChildren (cs₁ cs₂ : Array (Key s × Trie α s)) :
      Array (Key s × Trie α s) :=
    Array.mergeSortedMergingDuplicates
      (ord := ⟨compareOn (·.fst)⟩) cs₁ cs₂
      (fun (k₁, t₁) (_, t₂) => (k₁, mergePreservingDuplicates t₁ t₂))

  /-- The children of a path node -/
  pathChildren ks t : Array (Key s × Trie α s) :=
    -- by construction, ks is nonempty
    #[(ks.get! 0, mkPath (ks.extract 1 ks.size) t)]

  /-- smart constructor around `.path`, ensuring a path is nonempty -/
  mkPath ks t := if ks.isEmpty then t else .path ks t

  /-- smart constructor around `.branch`, ordering the keys correctly -/
  mkBranch2 (k1 : Key s) (t1 : Trie α s) (k2 : Key s) (t2 : Trie α s) : Trie α s:=
    if k1 < k2 then
      .branch #[(k1, t1), (k2, t2)]
    else
      .branch #[(k2, t2), (k1, t1)]


/--
Map a function over the arrays stored in the nodes of the tree.
-/
partial def mapArrays (d : Trie α s) (f : Array α → Array α) : Trie α s :=
  match d with
  | .empty => .empty
  | .values vs t => .values (f vs) (t.mapArrays f)
  | .path ks t => .path ks (t.mapArrays f)
  | .branch cs => .branch (cs.map fun (k, c) => (k, c.mapArrays f))

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
Map a function over the arrays stored in the nodes of the tree.
-/
def mapArrays (d : DiscrTree α s) (f : Array α → Array α) : DiscrTree α s :=
  ⟨ d.root.map (·.mapArrays f) ⟩

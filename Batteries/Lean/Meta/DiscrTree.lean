/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg, Kim Morrison
-/
module

public import Lean.Meta.DiscrTree
public import Batteries.Data.Array.Merge
public import Batteries.Lean.Meta.Expr
public import Batteries.Lean.PersistentHashMap

@[expose] public section

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

/-- Compute the length of the common prefix of two key arrays. -/
def commonPrefixLen (ks₁ ks₂ : Array Key) : Nat :=
  go 0
where
  go (i : Nat) : Nat :=
    if h₁ : i < ks₁.size then
      if _ : i < ks₂.size then
        if ks₁[i] == ks₂[i]! then go (i + 1) else i
      else i
    else i
  termination_by ks₁.size - i

/-- Create a `.path` for `ks[n+1:]` followed by `t`, or just `t` if no keys remain. -/
def restPath (ks : Array Key) (n : Nat) (t : Trie α) : Trie α :=
  if n + 1 < ks.size then .path (ks.extract (n + 1) ks.size) t else t

/-- Wrap a trie in a `.path` if the key array is non-empty. -/
def wrapPath (ks : Array Key) (t : Trie α) : Trie α :=
  if ks.isEmpty then t else .path ks t

/--
Merge two `Trie`s. Duplicate values are preserved.
-/
partial def mergePreservingDuplicates (t₁ t₂ : Trie α) : Trie α :=
  match t₁, t₂ with
  | .empty, t | t, .empty => t
  | .values vs₁ c₁, .values vs₂ c₂ =>
    .values (vs₁ ++ vs₂) (mergePreservingDuplicates c₁ c₂)
  | .values vs c, t | t, .values vs c =>
    .values vs (mergePreservingDuplicates c t)
  | .branch cs₁, .branch cs₂ =>
    .branch (mergeChildren cs₁ cs₂)
  | .branch cs, .path ks t | .path ks t, .branch cs =>
    mergePreservingDuplicates (.branch cs) (.branch #[(ks[0]!, restPath ks 0 t)])
  | .path ks₁ c₁, .path ks₂ c₂ =>
    let n := commonPrefixLen ks₁ ks₂
    if n == ks₁.size && n == ks₂.size then
      wrapPath ks₁ (mergePreservingDuplicates c₁ c₂)
    else if n == ks₁.size then
      wrapPath ks₁ (mergePreservingDuplicates c₁ (.path (ks₂.extract n ks₂.size) c₂))
    else if n == ks₂.size then
      wrapPath ks₂ (mergePreservingDuplicates (.path (ks₁.extract n ks₁.size) c₁) c₂)
    else
      let k₁ := ks₁[n]!; let k₂ := ks₂[n]!
      let t₁ := restPath ks₁ n c₁; let t₂ := restPath ks₂ n c₂
      let inner : Trie α := if k₁ < k₂ then .branch #[(k₁, t₁), (k₂, t₂)]
                             else .branch #[(k₂, t₂), (k₁, t₁)]
      wrapPath (ks₁.extract 0 n) inner
where
  /-- Merge two sorted child arrays. -/
  mergeChildren (cs₁ cs₂ : Array (Key × Trie α)) :
      Array (Key × Trie α) :=
    Array.mergeDedupWith
      (ord := ⟨compareOn (·.fst)⟩) cs₁ cs₂
      (fun (k₁, t₁) (_, t₂) => (k₁, mergePreservingDuplicates t₁ t₂))

end Trie

/--
Merge two `DiscrTree`s. Duplicate values are preserved.
-/
@[inline]
def mergePreservingDuplicates (t u : DiscrTree α) : DiscrTree α :=
  ⟨t.root.mergeWith u.root fun _ trie₁ trie₂ =>
    trie₁.mergePreservingDuplicates trie₂⟩

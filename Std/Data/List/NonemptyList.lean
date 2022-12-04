/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James Gallicchio
-/
import Std.Data.List.Basic

namespace Std

/--
`NonemptyList α` is isomorphic to a list with at least one element.
-/
structure NonemptyList (α : Type u) where
  /-- The head of the (non-empty) list. -/
  hd : α
  /-- The tail of the (non-empty) list. -/
  tl : List α
  deriving Inhabited

namespace NonemptyList

/-- Convert from a standard `List α`. Requires a proof that the list is nonempty,
which we attempt to close by `simp`. -/
def ofList (L : List α) (h : L ≠ [] := by simp) : NonemptyList α :=
  match L, h with
  | [],     _ => by contradiction
  | x::xs,  _ => ⟨x,xs⟩

-- TODO: is there a way to apply `ofList` as a coercion?

/-- Convert to a standard `List α`. -/
def toList : NonemptyList α → List α
| ⟨hd,tl⟩ => hd::tl

instance : CoeHead (NonemptyList α) (List α) where
  coe ne := ne.toList

instance [Repr α] : Repr (NonemptyList α) := ⟨(reprPrec ·.toList)⟩

instance [ToString α] : ToString (NonemptyList α) := ⟨(toString ·.toList)⟩

end NonemptyList

def List.nonempty? : List α → Option (NonemptyList α)
| [] => none
| hd::tl => some ⟨hd,tl⟩

def List.nonempty! [Inhabited α] : List α → NonemptyList α
| [] => panic! "nonempty! called on empty list D:"
| hd::tl => ⟨hd,tl⟩

namespace NonemptyList

def reduce (f : α → α → α) : NonemptyList α → α
| ⟨hd,tl⟩ => tl.foldl f hd

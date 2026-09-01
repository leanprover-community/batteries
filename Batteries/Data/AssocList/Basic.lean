/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Mario Carneiro
-/
module

public import Batteries.Data.List.Basic

@[expose] public section

/-!
# Association lists

`AssocList α β` is a `List (α × β)` with the pair structure flattened into the list constructor.
This file defines the type and its operations; the lemmas relating those operations to the
corresponding `List` operations along `AssocList.toList` are in `Batteries.Data.AssocList.Lemmas`.
-/

namespace Batteries

/--
`AssocList α β` is "the same as" `List (α × β)`, but flattening the structure
leads to one fewer pointer indirection (in the current code generator).
It is mainly intended as a component of `HashMap`, but it can also be used as a plain
key-value map.
-/
inductive AssocList (α : Type u) (β : Type v) where
  /-- An empty list -/
  | nil
  /-- Add a `key, value` pair to the list -/
  | cons (key : α) (value : β) (tail : AssocList α β)
  deriving Inhabited

namespace AssocList

/--
`O(n)`. Convert an `AssocList α β` into the equivalent `List (α × β)`.
This is used to give specifications for all the `AssocList` functions
in terms of corresponding list functions.
-/
@[simp] def toList : AssocList α β → List (α × β)
  | nil => []
  | cons a b es => (a, b) :: es.toList

instance : EmptyCollection (AssocList α β) := ⟨nil⟩

/-- `O(1)`. Is the list empty? -/
def isEmpty : AssocList α β → Bool
  | nil => true
  | _   => false

/-- The number of entries in an `AssocList`. -/
def length (L : AssocList α β) : Nat :=
  match L with
  | .nil => 0
  | .cons _ _ t => t.length + 1

/-- `O(n)`. Fold a monadic function over the list, from head to tail. -/
@[specialize] def foldlM [Monad m] (f : δ → α → β → m δ) : (init : δ) → AssocList α β → m δ
  | d, nil         => pure d
  | d, cons a b es => do foldlM f (← f d a b) es

/-- `O(n)`. Fold a function over the list, from head to tail. -/
@[inline] def foldl (f : δ → α → β → δ) (init : δ) (as : AssocList α β) : δ :=
  Id.run (foldlM (fun d a b => pure (f d a b)) init as)

@[simp] theorem foldlM_eq [Monad m] (f : δ → α → β → m δ) (init l) :
    foldlM f init l = l.toList.foldlM (fun d (a, b) => f d a b) init := by
  induction l generalizing init <;> simp [*, foldlM]

@[simp] theorem foldl_eq (f : δ → α → β → δ) (init l) :
    foldl f init l = l.toList.foldl (fun d (a, b) => f d a b) init := by
  simp [foldl, foldlM_eq]

/-- Optimized version of `toList`. -/
def toListTR (as : AssocList α β) : List (α × β) :=
  as.foldl (init := #[]) (fun r a b => r.push (a, b)) |>.toList

@[csimp] theorem toList_eq_toListTR : @toList = @toListTR := by
  funext α β as; simp [toListTR]

/-- `O(n)`. Run monadic function `f` on all elements in the list, from head to tail. -/
@[specialize] def forM [Monad m] (f : α → β → m PUnit) : AssocList α β → m PUnit
  | nil         => pure ⟨⟩
  | cons a b es => do f a b; forM f es

/-- `O(n)`. Map a function `f` over the keys of the list. -/
@[simp] def mapKey (f : α → δ) : AssocList α β → AssocList δ β
  | nil        => nil
  | cons k v t => cons (f k) v (mapKey f t)

/-- `O(n)`. Map a function `f` over the values of the list. -/
@[simp] def mapVal (f : α → β → δ) : AssocList α β → AssocList α δ
  | nil        => nil
  | cons k v t => cons k (f k v) (mapVal f t)

/-- `O(n)`. Returns the first entry in the list whose entry satisfies `p`. -/
@[specialize] def findEntryP? (p : α → β → Bool) : AssocList α β → Option (α × β)
  | nil         => none
  | cons k v es => bif p k v then some (k, v) else findEntryP? p es

/-- `O(n)`. Returns the first entry in the list whose key is equal to `a`. -/
@[inline] def findEntry? [BEq α] (a : α) (l : AssocList α β) : Option (α × β) :=
  findEntryP? (fun k _ => k == a) l

/-- `O(n)`. Returns the first value in the list whose key is equal to `a`. -/
def find? [BEq α] (a : α) : AssocList α β → Option β
  | nil         => none
  | cons k v es => match k == a with
    | true  => some v
    | false => find? a es

/-- `O(n)`. Returns true if any entry in the list satisfies `p`. -/
@[specialize] def any (p : α → β → Bool) : AssocList α β → Bool
  | nil         => false
  | cons k v es => p k v || any p es

/-- `O(n)`. Returns true if every entry in the list satisfies `p`. -/
@[specialize] def all (p : α → β → Bool) : AssocList α β → Bool
  | nil         => true
  | cons k v es => p k v && all p es

/-- Returns true if every entry in the list satisfies `p`. -/
def All (p : α → β → Prop) (l : AssocList α β) : Prop := ∀ a ∈ l.toList, p a.1 a.2

/-- `O(n)`. Returns true if there is an element in the list whose key is equal to `a`. -/
@[inline] def contains [BEq α] (a : α) (l : AssocList α β) : Bool := any (fun k _ => k == a) l

/--
`O(n)`. Replace the first entry in the list
with key equal to `a` to have key `a` and value `b`.
-/
@[simp] def replace [BEq α] (a : α) (b : β) : AssocList α β → AssocList α β
  | nil         => nil
  | cons k v es => match k == a with
    | true  => cons a b es
    | false => cons k v (replace a b es)

/-- `O(n)`. Remove the first entry in the list with key equal to `a`. -/
@[specialize, simp] def eraseP (p : α → β → Bool) : AssocList α β → AssocList α β
  | nil         => nil
  | cons k v es => bif p k v then es else cons k v (eraseP p es)

/-- `O(n)`. Remove the first entry in the list with key equal to `a`. -/
@[inline] def erase [BEq α] (a : α) (l : AssocList α β) : AssocList α β :=
  eraseP (fun k _ => k == a) l

/--
`O(n)`. Replace the first entry `a', b` in the list
with key equal to `a` to have key `a` and value `f a' b`.
-/
@[simp] def modify [BEq α] (a : α) (f : α → β → β) : AssocList α β → AssocList α β
  | nil         => nil
  | cons k v es => match k == a with
    | true  => cons a (f k v) es
    | false => cons k v (modify a f es)

/-- The implementation of `ForIn`, which enables `for (k, v) in aList do ...` notation. -/
@[specialize] protected def forIn [Monad m]
    (as : AssocList α β) (init : δ) (f : (α × β) → δ → m (ForInStep δ)) : m δ :=
  match as with
  | nil => pure init
  | cons k v es => do
    match (← f (k, v) init) with
    | ForInStep.done d  => pure d
    | ForInStep.yield d => es.forIn d f

instance [Monad m] : ForIn m (AssocList α β) (α × β) where
  forIn := AssocList.forIn

/-- Split the list into head and tail, if possible. -/
def pop? : AssocList α β → Option ((α × β) × AssocList α β)
  | nil => none
  | cons a b l => some ((a, b), l)

instance : Std.ToStream (AssocList α β) (AssocList α β) := ⟨fun x => x⟩
instance : Std.Stream (AssocList α β) (α × β) := ⟨pop?⟩

/-- Converts a list into an `AssocList`. This is the inverse function to `AssocList.toList`. -/
@[simp] def _root_.List.toAssocList : List (α × β) → AssocList α β
  | []          => nil
  | (a,b) :: es => cons a b (toAssocList es)

/-- Implementation of `==` on `AssocList`. -/
protected def beq [BEq α] [BEq β] : AssocList α β → AssocList α β → Bool
  | .nil, .nil => true
  | .cons _ _ _, .nil => false
  | .nil, .cons _ _ _ => false
  | .cons a b t, .cons a' b' t' => a == a' && b == b' && AssocList.beq t t'

/--
Boolean equality for `AssocList`.
(This relation cares about the ordering of the key-value pairs.)
-/
instance [BEq α] [BEq β] : BEq (AssocList α β) where beq := AssocList.beq

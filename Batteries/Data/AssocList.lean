/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Mario Carneiro
-/
import Batteries.Data.List.Basic

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

@[simp] theorem empty_eq : (∅ : AssocList α β) = nil := rfl

/-- `O(1)`. Is the list empty? -/
def isEmpty : AssocList α β → Bool
  | nil => true
  | _   => false

@[simp] theorem isEmpty_eq (l : AssocList α β) : isEmpty l = l.toList.isEmpty := by
  cases l <;> simp [*, isEmpty, List.isEmpty]

/-- The number of entries in an `AssocList`. -/
def length (L : AssocList α β) : Nat :=
  match L with
  | .nil => 0
  | .cons _ _ t => t.length + 1

@[simp] theorem length_nil : length (nil : AssocList α β) = 0 := rfl
@[simp] theorem length_cons : length (cons a b t) = length t + 1 := rfl

theorem length_toList (l : AssocList α β) : l.toList.length = l.length := by
  induction l <;> simp_all

/-- `O(n)`. Fold a monadic function over the list, from head to tail. -/
@[specialize] def foldlM [Monad m] (f : δ → α → β → m δ) : (init : δ) → AssocList α β → m δ
  | d, nil         => pure d
  | d, cons a b es => do foldlM f (← f d a b) es

@[simp] theorem foldlM_eq [Monad m] (f : δ → α → β → m δ) (init l) :
    foldlM f init l = l.toList.foldlM (fun d (a, b) => f d a b) init := by
  induction l generalizing init <;> simp [*, foldlM]

/-- `O(n)`. Fold a function over the list, from head to tail. -/
@[inline] def foldl (f : δ → α → β → δ) (init : δ) (as : AssocList α β) : δ :=
  Id.run (foldlM f init as)

@[simp] theorem foldl_eq (f : δ → α → β → δ) (init l) :
    foldl f init l = l.toList.foldl (fun d (a, b) => f d a b) init := by
  simp [List.foldl_eq_foldlM, foldl, Id.run]

/-- Optimized version of `toList`. -/
def toListTR (as : AssocList α β) : List (α × β) :=
  as.foldl (init := #[]) (fun r a b => r.push (a, b)) |>.toList

@[csimp] theorem toList_eq_toListTR : @toList = @toListTR := by
  funext α β as; simp [toListTR]
  exact .symm <| (Array.foldl_data_eq_map (toList as) _ id).trans (List.map_id _)

/-- `O(n)`. Run monadic function `f` on all elements in the list, from head to tail. -/
@[specialize] def forM [Monad m] (f : α → β → m PUnit) : AssocList α β → m PUnit
  | nil         => pure ⟨⟩
  | cons a b es => do f a b; forM f es

@[simp] theorem forM_eq [Monad m] (f : α → β → m PUnit) (l) :
    forM f l = l.toList.forM (fun (a, b) => f a b) := by
  induction l <;> simp [*, forM]

/-- `O(n)`. Map a function `f` over the keys of the list. -/
@[simp] def mapKey (f : α → δ) : AssocList α β → AssocList δ β
  | nil        => nil
  | cons k v t => cons (f k) v (mapKey f t)

@[simp] theorem toList_mapKey (f : α → δ) (l : AssocList α β) :
    (mapKey f l).toList = l.toList.map (fun (a, b) => (f a, b)) := by
  induction l <;> simp [*]

@[simp] theorem length_mapKey : (mapKey f l).length = l.length := by
  induction l <;> simp_all

/-- `O(n)`. Map a function `f` over the values of the list. -/
@[simp] def mapVal (f : α → β → δ) : AssocList α β → AssocList α δ
  | nil        => nil
  | cons k v t => cons k (f k v) (mapVal f t)

@[simp] theorem toList_mapVal (f : α → β → δ) (l : AssocList α β) :
    (mapVal f l).toList = l.toList.map (fun (a, b) => (a, f a b)) := by
  induction l <;> simp [*]

@[simp] theorem length_mapVal : (mapVal f l).length = l.length := by
  induction l <;> simp_all

/-- `O(n)`. Returns the first entry in the list whose entry satisfies `p`. -/
@[specialize] def findEntryP? (p : α → β → Bool) : AssocList α β → Option (α × β)
  | nil         => none
  | cons k v es => bif p k v then some (k, v) else findEntryP? p es

@[simp] theorem findEntryP?_eq (p : α → β → Bool) (l : AssocList α β) :
    findEntryP? p l = l.toList.find? fun (a, b) => p a b := by
  induction l <;> simp [findEntryP?, List.find?_cons]; split <;> simp [*]

/-- `O(n)`. Returns the first entry in the list whose key is equal to `a`. -/
@[inline] def findEntry? [BEq α] (a : α) (l : AssocList α β) : Option (α × β) :=
  findEntryP? (fun k _ => k == a) l

@[simp] theorem findEntry?_eq [BEq α] (a : α) (l : AssocList α β) :
    findEntry? a l = l.toList.find? (·.1 == a) := findEntryP?_eq ..

/-- `O(n)`. Returns the first value in the list whose key is equal to `a`. -/
def find? [BEq α] (a : α) : AssocList α β → Option β
  | nil         => none
  | cons k v es => match k == a with
    | true  => some v
    | false => find? a es

theorem find?_eq_findEntry? [BEq α] (a : α) (l : AssocList α β) :
    find? a l = (l.findEntry? a).map (·.2) := by
  induction l <;> simp [find?, List.find?_cons]; split <;> simp [*]

@[simp] theorem find?_eq [BEq α] (a : α) (l : AssocList α β) :
    find? a l = (l.toList.find? (·.1 == a)).map (·.2) := by simp [find?_eq_findEntry?]

/-- `O(n)`. Returns true if any entry in the list satisfies `p`. -/
@[specialize] def any (p : α → β → Bool) : AssocList α β → Bool
  | nil         => false
  | cons k v es => p k v || any p es

@[simp] theorem any_eq (p : α → β → Bool) (l : AssocList α β) :
    any p l = l.toList.any fun (a, b) => p a b := by induction l <;> simp [any, *]

/-- `O(n)`. Returns true if every entry in the list satisfies `p`. -/
@[specialize] def all (p : α → β → Bool) : AssocList α β → Bool
  | nil         => true
  | cons k v es => p k v && all p es

@[simp] theorem all_eq (p : α → β → Bool) (l : AssocList α β) :
    all p l = l.toList.all fun (a, b) => p a b := by induction l <;> simp [all, *]

/-- Returns true if every entry in the list satisfies `p`. -/
def All (p : α → β → Prop) (l : AssocList α β) : Prop := ∀ a ∈ l.toList, p a.1 a.2

/-- `O(n)`. Returns true if there is an element in the list whose key is equal to `a`. -/
@[inline] def contains [BEq α] (a : α) (l : AssocList α β) : Bool := any (fun k _ => k == a) l

@[simp] theorem contains_eq [BEq α] (a : α) (l : AssocList α β) :
    contains a l = l.toList.any (·.1 == a) := by
  induction l <;> simp [*, contains]

/--
`O(n)`. Replace the first entry in the list
with key equal to `a` to have key `a` and value `b`.
-/
@[simp] def replace [BEq α] (a : α) (b : β) : AssocList α β → AssocList α β
  | nil         => nil
  | cons k v es => match k == a with
    | true  => cons a b es
    | false => cons k v (replace a b es)

@[simp] theorem toList_replace [BEq α] (a : α) (b : β) (l : AssocList α β) :
    (replace a b l).toList =
    l.toList.replaceF (bif ·.1 == a then some (a, b) else none) := by
  induction l <;> simp [replace]; split <;> simp [*]

@[simp] theorem length_replace [BEq α] {a : α} : (replace a b l).length = l.length := by
  induction l
  · rfl
  · simp only [replace, length_cons]
    split <;> simp_all

/-- `O(n)`. Remove the first entry in the list with key equal to `a`. -/
@[specialize, simp] def eraseP (p : α → β → Bool) : AssocList α β → AssocList α β
  | nil         => nil
  | cons k v es => bif p k v then es else cons k v (eraseP p es)

@[simp] theorem toList_eraseP (p) (l : AssocList α β) :
    (eraseP p l).toList = l.toList.eraseP fun (a, b) => p a b := by
  induction l <;> simp [List.eraseP, cond]; split <;> simp [*]

/-- `O(n)`. Remove the first entry in the list with key equal to `a`. -/
@[inline] def erase [BEq α] (a : α) (l : AssocList α β) : AssocList α β :=
  eraseP (fun k _ => k == a) l

@[simp] theorem toList_erase [BEq α] (a : α) (l : AssocList α β) :
    (erase a l).toList = l.toList.eraseP (·.1 == a) := toList_eraseP ..

/--
`O(n)`. Replace the first entry `a', b` in the list
with key equal to `a` to have key `a` and value `f a' b`.
-/
@[simp] def modify [BEq α] (a : α) (f : α → β → β) : AssocList α β → AssocList α β
  | nil         => nil
  | cons k v es => match k == a with
    | true  => cons a (f k v) es
    | false => cons k v (modify a f es)

@[simp] theorem toList_modify [BEq α] (a : α) (l : AssocList α β) :
    (modify a f l).toList =
    l.toList.replaceF fun (k, v) => bif k == a then some (a, f k v) else none := by
  simp [cond]
  induction l with simp [List.replaceF]
  | cons k v es ih => cases k == a <;> simp [ih]

@[simp] theorem length_modify [BEq α] {a : α} : (modify a f l).length = l.length := by
  induction l
  · rfl
  · simp only [modify, length_cons]
    split <;> simp_all

/-- The implementation of `ForIn`, which enables `for (k, v) in aList do ...` notation. -/
@[specialize] protected def forIn [Monad m]
    (as : AssocList α β) (init : δ) (f : (α × β) → δ → m (ForInStep δ)) : m δ :=
  match as with
  | nil => pure init
  | cons k v es => do
    match (← f (k, v) init) with
    | ForInStep.done d  => pure d
    | ForInStep.yield d => es.forIn d f

instance : ForIn m (AssocList α β) (α × β) where
  forIn := AssocList.forIn

@[simp] theorem forIn_eq [Monad m] (l : AssocList α β) (init : δ)
    (f : (α × β) → δ → m (ForInStep δ)) : forIn l init f = forIn l.toList init f := by
  simp [forIn, List.forIn]
  induction l generalizing init <;> simp [AssocList.forIn, List.forIn.loop]
  congr; funext a; split <;> simp [*]

/-- Split the list into head and tail, if possible. -/
def pop? : AssocList α β → Option ((α × β) × AssocList α β)
  | nil => none
  | cons a b l => some ((a, b), l)

instance : ToStream (AssocList α β) (AssocList α β) := ⟨fun x => x⟩
instance : Stream (AssocList α β) (α × β) := ⟨pop?⟩

/-- Converts a list into an `AssocList`. This is the inverse function to `AssocList.toList`. -/
@[simp] def _root_.List.toAssocList : List (α × β) → AssocList α β
  | []          => nil
  | (a,b) :: es => cons a b (toAssocList es)

@[simp] theorem _root_.List.toList_toAssocList (l : List (α × β)) : l.toAssocList.toList = l := by
  induction l <;> simp [*]

@[simp] theorem toList_toAssocList (l : AssocList α β) : l.toList.toAssocList = l := by
  induction l <;> simp [*]

@[simp] theorem _root_.List.length_toAssocList (l : List (α × β)) :
    l.toAssocList.length = l.length := by
  induction l <;> simp [*]

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

@[simp] theorem beq_nil₂ [BEq α] [BEq β] : ((.nil : AssocList α β) == .nil) = true := rfl
@[simp] theorem beq_nil_cons [BEq α] [BEq β] : ((.nil : AssocList α β) == .cons a b t) = false :=
  rfl
@[simp] theorem beq_cons_nil [BEq α] [BEq β] : ((.cons a b t : AssocList α β) == .nil) = false :=
  rfl
@[simp] theorem beq_cons₂ [BEq α] [BEq β] :
    ((.cons a b t : AssocList α β) == .cons a' b' t') = (a == a' && b == b' && t == t') := rfl

instance [BEq α] [LawfulBEq α] [BEq β] [LawfulBEq β] : LawfulBEq (AssocList α β) where
  rfl {L} := by induction L <;> simp_all
  eq_of_beq {L M} := by
    induction L generalizing M with
    | nil => cases M <;> simp_all
    | cons a b L ih =>
      cases M with
      | nil => simp_all
      | cons a' b' M =>
        simp_all only [beq_cons₂, Bool.and_eq_true, beq_iff_eq, cons.injEq, true_and, and_imp]
        exact fun _ _ => ih

protected theorem beq_eq [BEq α] [BEq β] {l m : AssocList α β} :
    (l == m) = (l.toList == m.toList) := by
  simp [(· == ·)]
  induction l generalizing m <;> cases m <;> simp [*, (· == ·), AssocList.beq, List.beq]

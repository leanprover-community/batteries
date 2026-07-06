/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jannis Limperg, Mario Carneiro
-/
module

public import Batteries.Classes.Order
public import Batteries.Control.ForInStep.Basic
import Std.Data.DTreeMap.Internal.Balancing

@[expose] public section

namespace Batteries
namespace BinomialHeap
namespace Imp

/--
A `HeapNode` is one of the internal nodes of the binomial heap.
It is always a perfect binary tree, with the depth of the tree stored in the `Heap`.
However the interpretation of the two pointers is different: we view the `child`
as going to the first child of this node, and `sibling` goes to the next sibling
of this tree. So it actually encodes a forest where each node has children
`node.child`, `node.child.sibling`, `node.child.sibling.sibling`, etc.

Each edge in this forest denotes a `le a b` relation that has been checked, so
the root is smaller than everything else under it.
-/
inductive HeapNode (α : Type u) where
  /-- An empty forest, which has depth `0`. -/
  | nil : HeapNode α
  /-- A forest of rank `r + 1` consists of a root `a`,
  a forest `child` of rank `r` elements greater than `a`,
  and another forest `sibling` of rank `r`. -/
  | node (a : α) (child sibling : HeapNode α) : HeapNode α
  deriving Repr

/--
The "real size" of the node, counting up how many values of type `α` are stored.
This is `O(n)` and is intended mainly for specification purposes.
For a well formed `HeapNode` the size is always `2^n - 1` where `n` is the depth.
-/
@[simp] def HeapNode.realSize : HeapNode α → Nat
  | .nil => 0
  | .node _ c s => c.realSize + 1 + s.realSize

/-- A node containing a single element `a`. -/
def HeapNode.singleton (a : α) : HeapNode α := .node a .nil .nil

/--
`O(log n)`. The rank, or the number of trees in the forest.
It is also the depth of the forest.
-/
def HeapNode.rank : HeapNode α → Nat
  | .nil => 0
  | .node _ _ s => s.rank + 1

/-- Tail-recursive version of `HeapNode.rank`. -/
@[inline] def HeapNode.rankTR (s : HeapNode α) : Nat := go s 0 where
  /-- Computes `s.rank + r` -/
  go : HeapNode α → Nat → Nat
  | .nil, r => r
  | .node _ _ s, r => go s (r + 1)

@[csimp] theorem HeapNode.rankTR_eq : @rankTR = @rank := by
  funext α s; exact go s 0
where
  go {α} : ∀ s n, @rankTR.go α s n = rank s + n
  | .nil, _ => (Nat.zero_add ..).symm
  | .node .., _ => by simp +arith only [rankTR.go, go, rank]

/--
A `Heap` is the top level structure in a binomial heap.
It consists of a forest of `HeapNode`s with strictly increasing ranks.
-/
inductive Heap (α : Type u) where
  /-- An empty heap. -/
  | nil : Heap α
  /-- A cons node contains a tree of root `val`, children `node` and rank `rank`,
  and then `next` which is the rest of the forest. -/
  | cons (rank : Nat) (val : α) (node : HeapNode α) (next : Heap α) : Heap α
  deriving Repr

/--
`O(n)`. The "real size" of the heap, counting up how many values of type `α` are stored.
This is intended mainly for specification purposes.
Prefer `Heap.size`, which is the same for well formed heaps.
-/
@[simp] def Heap.realSize : Heap α → Nat
  | .nil => 0
  | .cons _ _ c s => c.realSize + 1 + s.realSize

/-- `O(log n)`. The number of elements in the heap. -/
def Heap.size : Heap α → Nat
  | .nil => 0
  | .cons r _ _ s => 1 <<< r + s.size

/-- `O(1)`. Is the heap empty? -/
@[inline] def Heap.isEmpty : Heap α → Bool
  | .nil => true
  | _    => false

/-- `O(1)`. The heap containing a single value `a`. -/
@[inline] def Heap.singleton (a : α) : Heap α := .cons 0 a .nil .nil

/-- `O(1)`. Auxiliary for `Heap.merge`: Is the minimum rank in `Heap` strictly larger than `n`? -/
def Heap.rankGT : Heap α → Nat → Prop
  | .nil, _ => True
  | .cons r .., n => n < r

instance : Decidable (Heap.rankGT s n) :=
  match s with
  | .nil => inferInstanceAs (Decidable True)
  | .cons .. => inferInstanceAs (Decidable (_ < _))

/-- `O(log n)`. The number of trees in the forest. -/
@[simp] def Heap.length : Heap α → Nat
  | .nil => 0
  | .cons _ _ _ r => r.length + 1

/--
`O(1)`. Auxiliary for `Heap.merge`: combines two heap nodes of the same rank
into one with the next larger rank.
-/
@[inline] def combine (le : α → α → Bool) (a₁ a₂ : α) (n₁ n₂ : HeapNode α) : α × HeapNode α :=
  if le a₁ a₂ then (a₁, .node a₂ n₂ n₁) else (a₂, .node a₁ n₁ n₂)

/--
Merge two forests of binomial trees. The forests are assumed to be ordered
by rank and `merge` maintains this invariant.
-/
@[specialize] def Heap.merge (le : α → α → Bool) : Heap α → Heap α → Heap α
  | .nil, h  => h
  | h,  .nil => h
  | s₁@(.cons r₁ a₁ n₁ t₁), s₂@(.cons r₂ a₂ n₂ t₂) =>
    if r₁ < r₂ then .cons r₁ a₁ n₁ (merge le t₁ s₂)
    else if r₂ < r₁ then .cons r₂ a₂ n₂ (merge le s₁ t₂)
    else
      let (a, n) := combine le a₁ a₂ n₁ n₂
      let r := r₁ + 1
      if t₁.rankGT r then if t₂.rankGT r
        then .cons r a n (merge le t₁ t₂)
        else merge le (.cons r a n t₁) t₂
      else if t₂.rankGT r
        then merge le t₁ (.cons r a n t₂)
        else .cons r a n (merge le t₁ t₂)
termination_by s₁ s₂ => s₁.length + s₂.length

/--
`O(log n)`. Convert a `HeapNode` to a `Heap` by reversing the order of the nodes
along the `sibling` spine.
-/
def HeapNode.toHeap (s : HeapNode α) : Heap α := go s s.rank .nil where
  /-- Computes `s.toHeap ++ res` tail-recursively, assuming `n = s.rank`. -/
  go : HeapNode α → Nat → Heap α → Heap α
  | .nil, _, res => res
  | .node a c s, n, res => go s (n - 1) (.cons (n - 1) a c res)

/-- `O(log n)`. Get the smallest element in the heap, including the passed in value `a`. -/
@[specialize] def Heap.headD (le : α → α → Bool) (a : α) : Heap α → α
  | .nil => a
  | .cons _ b _ hs => headD le (if le a b then a else b) hs

/-- `O(log n)`. Get the smallest element in the heap, if it has an element. -/
@[inline] def Heap.head? (le : α → α → Bool) : Heap α → Option α
  | .nil => none
  | .cons _ h _ hs => some <| headD le h hs

/--
The return type of `FindMin`, which encodes various quantities needed to
reconstruct the tree in `deleteMin`.
-/
structure FindMin (α) where
  /-- The list of elements prior to the minimum element, encoded as a "difference list". -/
  before : Heap α → Heap α := id
  /-- The minimum element. -/
  val : α
  /-- The children of the minimum element. -/
  node : HeapNode α
  /-- The forest after the minimum element. -/
  next : Heap α

/--
`O(log n)`. Find the minimum element, and return a data structure `FindMin` with information
needed to reconstruct the rest of the binomial heap.
-/
@[specialize] def Heap.findMin (le : α → α → Bool) (k : Heap α → Heap α) :
    Heap α → FindMin α → FindMin α
  | .nil, res => res
  | .cons r a c s, res =>
    -- It is important that we check `le res.val a` here, not the other way
    -- around. This ensures that head? and findMin find the same element even
    -- when we have `le res.val a` and `le a res.val` (i.e. le is not antisymmetric).
    findMin le (k ∘ .cons r a c) s <| if le res.val a then res else ⟨k, a, c, s⟩

/-- `O(log n)`. Find and remove the the minimum element from the binomial heap. -/
def Heap.deleteMin (le : α → α → Bool) : Heap α → Option (α × Heap α)
  | .nil => none
  | .cons r a c s =>
    let { before, val, node, next } := findMin le (.cons r a c) s ⟨id, a, c, s⟩
    some (val, node.toHeap.merge le (before next))

/-- `O(log n)`. Get the tail of the binomial heap after removing the minimum element. -/
@[inline] def Heap.tail? (le : α → α → Bool) (h : Heap α) : Option (Heap α) :=
  deleteMin le h |>.map (·.snd)

/-- `O(log n)`. Remove the minimum element of the heap. -/
@[inline] def Heap.tail (le : α → α → Bool) (h : Heap α) : Heap α := tail? le h |>.getD .nil

theorem Heap.realSize_merge (le) (s₁ s₂ : Heap α) :
    (s₁.merge le s₂).realSize = s₁.realSize + s₂.realSize := by
  unfold merge; split
  · simp
  · simp
  · next r₁ a₁ n₁ t₁ r₂ a₂ n₂ t₂ =>
    have IH₁ r a n := realSize_merge le t₁ (cons r a n t₂)
    have IH₂ r a n := realSize_merge le (cons r a n t₁) t₂
    have IH₃ := realSize_merge le t₁ t₂
    split; · simp [IH₁, Nat.add_assoc]
    split; · simp [IH₂, Nat.add_assoc, Nat.add_left_comm]
    split; simp only; rename_i a n eq
    have : n.realSize = n₁.realSize + 1 + n₂.realSize := by
      rw [combine] at eq; split at eq <;> cases eq <;>
        simp [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
    split <;> split <;> simp [IH₁, IH₂, IH₃, this, Nat.add_assoc, Nat.add_left_comm]
termination_by s₁.length + s₂.length

private def FindMin.HasSize (res : FindMin α) (n : Nat) : Prop :=
  ∃ m,
    (∀ s, (res.before s).realSize = m + s.realSize) ∧
    n = m + res.node.realSize + res.next.realSize + 1

private theorem Heap.realSize_findMin {s : Heap α}
    (m) (hk : ∀ s, (k s).realSize = m + s.realSize)
    (eq : n = m + s.realSize) (hres : res.HasSize n) :
    (s.findMin le k res).HasSize n :=
  match s with
  | .nil => hres
  | .cons r a c s => by
    simp [findMin]
    refine realSize_findMin (m + c.realSize + 1)
      (by simp [hk, Nat.add_assoc]) (by simp [eq, Nat.add_assoc]) ?_
    split
    · exact hres
    · exact ⟨m, hk, by simp [eq, Nat.add_comm, Nat.add_left_comm]⟩

theorem HeapNode.realSize_toHeap (s : HeapNode α) : s.toHeap.realSize = s.realSize := go s where
  go {n res} : ∀ s : HeapNode α, (toHeap.go s n res).realSize = s.realSize + res.realSize
  | .nil => (Nat.zero_add _).symm
  | .node a c s => by simp [toHeap.go, go, Nat.add_assoc, Nat.add_left_comm]

theorem Heap.realSize_deleteMin {s : Heap α} (eq : s.deleteMin le = some (a, s')) :
    s.realSize = s'.realSize + 1 := by
  cases s with cases eq | cons r a c s => ?_
  have : (s.findMin le (cons r a c) ⟨id, a, c, s⟩).HasSize (c.realSize + s.realSize + 1) :=
    Heap.realSize_findMin (c.realSize + 1) (by simp) (Nat.add_right_comm ..) ⟨0, by simp⟩
  revert this
  match s.findMin le (cons r a c) ⟨id, a, c, s⟩ with
  | { before, val, node, next } =>
    intro ⟨m, ih₁, ih₂⟩; dsimp only at ih₁ ih₂
    rw [realSize, Nat.add_right_comm, ih₂]
    simp only [realSize_merge, HeapNode.realSize_toHeap, ih₁, Nat.add_assoc, Nat.add_left_comm]

theorem Heap.realSize_tail? {s : Heap α} : s.tail? le = some s' →
    s.realSize = s'.realSize + 1 := by
  simp only [Heap.tail?]; intro eq
  match eq₂ : s.deleteMin le, eq with
  | some (a, tl), rfl => exact realSize_deleteMin eq₂

theorem Heap.realSize_tail (le) (s : Heap α) : (s.tail le).realSize = s.realSize - 1 := by
  simp only [Heap.tail]
  match eq : s.tail? le with
  | none => cases s with cases eq | nil => rfl
  | some tl => simp [Heap.realSize_tail? eq]

/--
`O(n log n)`. Monadic fold over the elements of a heap in increasing order,
by repeatedly pulling the minimum element out of the heap.
-/
@[specialize] def Heap.foldM [Monad m] (le : α → α → Bool) (s : Heap α)
    (init : β) (f : β → α → m β) : m β :=
  match eq : s.deleteMin le with
  | none => pure init
  | some (hd, tl) => do
    have : tl.realSize < s.realSize := by simp +arith [Heap.realSize_deleteMin eq]
    foldM le tl (← f init hd) f
termination_by s.realSize

/--
`O(n log n)`. Fold over the elements of a heap in increasing order,
by repeatedly pulling the minimum element out of the heap.
-/
@[inline] def Heap.fold (le : α → α → Bool) (s : Heap α) (init : β) (f : β → α → β) : β :=
  Id.run <| s.foldM le init f

/-- `O(n log n)`. Convert the heap to an array in increasing order. -/
@[inline] def Heap.toArray (le : α → α → Bool) (s : Heap α) : Array α := fold le s #[] Array.push

/-- `O(n log n)`. Convert the heap to a list in increasing order. -/
@[inline] def Heap.toList (le : α → α → Bool) (s : Heap α) : List α := (s.toArray le).toList

section
variable [Monad m] (nil : β) (join : α → β → β → m β)

/-- `O(n)`. Fold a monadic function over the tree structure to accumulate a value. -/
@[specialize] def HeapNode.foldTreeM : HeapNode α → m β
  | .nil => pure nil
  | .node a c s => do join a (← c.foldTreeM) (← s.foldTreeM)

/-- `O(n)`. Fold a monadic function over the tree structure to accumulate a value. -/
@[specialize] def Heap.foldTreeM : Heap α → m β
  | .nil => pure nil
  | .cons _ a c s => do join a (← c.foldTreeM nil join) (← s.foldTreeM)

end

/-- `O(n)`. Fold a function over the tree structure to accumulate a value. -/
@[inline] def Heap.foldTree (nil : β) (join : α → β → β → β) (s : Heap α) : β :=
  Id.run <| s.foldTreeM nil join

/-- `O(n)`. Convert the heap to a list in arbitrary order. -/
def Heap.toListUnordered (s : Heap α) : List α :=
  s.foldTree id (fun a c s l => a :: c (s l)) []

/-- `O(n)`. Convert the heap to an array in arbitrary order. -/
def Heap.toArrayUnordered (s : Heap α) : Array α :=
  s.foldTree id (fun a c s r => s (c (r.push a))) #[]

/--
The well formedness predicate for a heap node.
It asserts that:
* If `a` is added at the top to make the forest into a tree, the resulting tree
  is a `le`-min-heap (if `le` is well-behaved)
* When interpreting `child` and `sibling` as left and right children of a binary tree,
  it is a perfect binary tree with depth `r`
-/
def HeapNode.WF (le : α → α → Bool) (a : α) : HeapNode α → Nat → Prop
  | .nil, r => r = 0
  | .node b c s, r => ∃ r', r = r' + 1 ∧ (∀ [TotalBLE le], le a b) ∧ c.WF le b r' ∧ s.WF le a r'

/--
The well formedness predicate for a binomial heap.
It asserts that:
* It consists of a list of well formed trees with the specified ranks
* The ranks are in strictly increasing order, and all are at least `n`
-/
def Heap.WF (le : α → α → Bool) (n : Nat) : Heap α → Prop
  | .nil => True
  | .cons r a c s => n ≤ r ∧ c.WF le a r ∧ s.WF le (r+1)

theorem Heap.WF.nil : Heap.nil.WF le n := trivial

theorem Heap.WF.singleton : (Heap.singleton a).WF le 0 := ⟨by decide, rfl, ⟨⟩⟩

theorem Heap.WF.of_rankGT (hlt : s.rankGT n) (h : Heap.WF le n' s) : s.WF le (n+1) :=
  match s with
  | .nil => trivial
  | .cons .. => let ⟨_, h₂, h₃⟩ := h; ⟨hlt, h₂, h₃⟩

theorem Heap.WF.of_le (hle : n ≤ n') (h : Heap.WF le n' s) : s.WF le n :=
  match s with
  | .nil => trivial
  | .cons .. => let ⟨h₁, h₂, h₃⟩ := h; ⟨Nat.le_trans hle h₁, h₂, h₃⟩

theorem Heap.rankGT.of_le (h : Heap.rankGT s n) (h' : n' ≤ n) : s.rankGT n' :=
  match s with
  | .nil => trivial
  | .cons .. => Nat.lt_of_le_of_lt h' h

theorem Heap.WF.rankGT (h : Heap.WF lt (n+1) s) : s.rankGT n :=
  match s with
  | .nil => trivial
  | .cons .. => Nat.lt_of_succ_le h.1

theorem Heap.WF.merge' (h₁ : s₁.WF le n) (h₂ : s₂.WF le n) :
    (merge le s₁ s₂).WF le n ∧ ((s₁.rankGT n ↔ s₂.rankGT n) → (merge le s₁ s₂).rankGT n) := by
  unfold merge; split
  · exact ⟨h₂, fun h => h.1 h₁⟩
  · exact ⟨h₁, fun h => h.2 h₂⟩
  · rename_i r₁ a₁ n₁ t₁ r₂ a₂ n₂ t₂
    let ⟨hr₁, hn₁, ht₁⟩ := h₁
    let ⟨hr₂, hn₂, ht₂⟩ := h₂
    split <;> rename_i lt₁
    · refine ⟨⟨hr₁, hn₁, And.left (merge' ht₁ ⟨lt₁, hn₂, ht₂⟩)⟩, fun h => ?_⟩
      exact h.2 <| Nat.lt_of_le_of_lt hr₁ lt₁
    split <;> rename_i lt₂
    · refine ⟨⟨hr₂, hn₂, And.left (merge' ⟨lt₂, hn₁, ht₁⟩ ht₂)⟩, fun h => ?_⟩
      exact h.1 <| Nat.lt_of_le_of_lt hr₂ lt₂
    cases Nat.le_antisymm (Nat.ge_of_not_lt lt₂) (Nat.ge_of_not_lt lt₁)
    split; rename_i a n eq
    have : n.WF le a (r₁+1) := by
      unfold combine at eq; split at eq <;> cases eq <;> rename_i h
      · exact ⟨r₁, rfl, h, hn₂, hn₁⟩
      · exact ⟨r₁, rfl, TotalBLE.total.resolve_left h, hn₁, hn₂⟩
    simp only; split <;> split <;> rename_i hl₁ hl₂
    · exact ⟨⟨Nat.le_succ_of_le hr₁, this,
        (merge' (ht₁.of_rankGT hl₁) (ht₂.of_rankGT hl₂)).1⟩,
        fun _ => Nat.lt_succ_of_le hr₁⟩
    · let ⟨ih₁, ih₂⟩ := merge' (s₁ := .cons ..)
        ⟨Nat.le_succ_of_le hr₁, this, ht₁.of_rankGT hl₁⟩
        (ht₂.of_le (Nat.le_succ_of_le hr₁))
      exact ⟨ih₁, fun _ => ih₂ ⟨fun _ => ht₂.rankGT.of_le hr₁, fun _ => Nat.lt_succ_of_le hr₁⟩⟩
    · let ⟨ih₁, ih₂⟩ := merge' (s₂ := .cons ..) (ht₁.of_le (Nat.le_succ_of_le hr₁))
        ⟨Nat.le_succ_of_le hr₁, this, ht₂.of_rankGT hl₂⟩
      exact ⟨ih₁, fun _ => ih₂ ⟨fun _ => Nat.lt_succ_of_le hr₁, fun _ => ht₁.rankGT.of_le hr₁⟩⟩
    · let ⟨ih₁, ih₂⟩ := merge' ht₁ ht₂
      exact ⟨⟨Nat.le_succ_of_le hr₁, this, ih₁.of_rankGT (ih₂ (iff_of_false hl₁ hl₂))⟩,
        fun _ => Nat.lt_succ_of_le hr₁⟩
termination_by s₁.length + s₂.length

theorem Heap.WF.merge (h₁ : s₁.WF le n) (h₂ : s₂.WF le n) : (merge le s₁ s₂).WF le n :=
  (merge' h₁ h₂).1

theorem HeapNode.WF.rank_eq : ∀ {n} {s : HeapNode α}, s.WF le a n → s.rank = n
  | _, .nil, h => h.symm
  | _, .node .., ⟨_, rfl, _, _, h⟩ => congrArg Nat.succ (rank_eq h)

theorem HeapNode.WF.toHeap {s : HeapNode α} (h : s.WF le a n) : s.toHeap.WF le 0 :=
  go h trivial
where
  go {res} : ∀ {n s}, s.WF le a n → res.WF le s.rank → (HeapNode.toHeap.go s s.rank res).WF le 0
  | _, .nil, _, hr => hr
  | _, .node a c s, ⟨n, rfl, _, h, h'⟩, hr =>
    go (s := s) h' ⟨Nat.le_refl _, by rw [← h'.rank_eq] at h; exact h, hr⟩

/--
The well formedness predicate for a `FindMin` value.
This is not actually a predicate, as it contains an additional data value
`rank` corresponding to the rank of the returned node, which is omitted from `findMin`.
-/
structure FindMin.WF (le : α → α → Bool) (res : FindMin α) where
  /-- The rank of the minimum element -/
  rank : Nat
  /-- `before` is a difference list which can be appended to a binomial heap
  with ranks at least `rank` to produce another well formed heap. -/
  before : ∀ {s}, s.WF le rank → (res.before s).WF le 0
  /-- `node` is a well formed forest of rank `rank` with `val` at the root. -/
  node : res.node.WF le res.val rank
  /-- `next` is a binomial heap with ranks above `rank + 1`. -/
  next : res.next.WF le (rank + 1)

/-- The conditions under which `findMin` is well-formed. -/
def Heap.WF.findMin {s : Heap α} (h : s.WF le n) (hr : res.WF le)
    (hk : ∀ {s}, s.WF le n → (k s).WF le 0) : ((s : Heap α).findMin le k res).WF le :=
  match s with
  | .nil => hr
  | .cons r a c s => by
    let ⟨h₁, h₂, h₃⟩ := h
    simp [Heap.findMin]
    cases le res.val a with
    | true  => exact findMin h₃ hr (fun h => hk ⟨h₁, h₂, h⟩)
    | false => exact findMin h₃ ⟨_, fun h => hk (h.of_le h₁), h₂, h₃⟩ (fun h => hk ⟨h₁, h₂, h⟩)

theorem Heap.WF.deleteMin {s : Heap α}
    (h : s.WF le n) (eq : s.deleteMin le = some (a, s')) : s'.WF le 0 := by
  cases s with cases eq | cons r a c s => ?_
  have : (s.findMin le (cons r a c) ⟨id, a, c, s⟩).WF le :=
    let ⟨_, h₂, h₃⟩ := h
    h₃.findMin ⟨_, fun h => h.of_le (Nat.zero_le _), h₂, h₃⟩
      fun h => ⟨Nat.zero_le _, h₂, h⟩
  revert this
  let { before, val, node, next } := s.findMin le (cons r a c) ⟨id, a, c, s⟩
  intro ⟨_, hk, ih₁, ih₂⟩
  exact ih₁.toHeap.merge <| hk (ih₂.of_le (Nat.le_succ _))

theorem Heap.WF.tail? (hwf : (s : Heap α).WF le n) : s.tail? le = some tl → tl.WF le 0 := by
  simp only [Heap.tail?]; intro eq
  match eq₂ : s.deleteMin le, eq with
  | some (a, tl), rfl => exact hwf.deleteMin eq₂

theorem Heap.WF.tail (hwf : (s : Heap α).WF le n) : (s.tail le).WF le 0 := by
  simp only [Heap.tail]
  match eq : s.tail? le with
  | none => exact Heap.WF.nil
  | some tl => exact hwf.tail? eq

end Imp
end BinomialHeap

open BinomialHeap.Imp

/--
A [binomial heap](https://en.wikipedia.org/wiki/Binomial_heap) is a data structure which supports
the following primary operations:

* `insert : α → BinomialHeap α → BinomialHeap α`: add an element to the heap
* `deleteMin : BinomialHeap α → Option (α × BinomialHeap α)`:
  remove the minimum element from the heap
* `merge : BinomialHeap α → BinomialHeap α → BinomialHeap α`: combine two heaps

The first two operations are known as a "priority queue", so this could be called
a "mergeable priority queue". The standard choice for a priority queue is a binary heap,
which supports `insert` and `deleteMin` in `O(log n)`, but `merge` is `O(n)`.
With a `BinomialHeap`, all three operations are `O(log n)`.
-/
def BinomialHeap (α : Type u) (le : α → α → Bool) :=
  { h : Heap α // h.WF le 0 }

/-- `O(1)`. Make a new empty binomial heap. -/
@[inline] def mkBinomialHeap (α : Type u) (le : α → α → Bool) : BinomialHeap α le :=
  ⟨.nil, Heap.WF.nil⟩

namespace BinomialHeap
variable {α : Type u} {le : α → α → Bool}

/-- `O(1)`. Make a new empty binomial heap. -/
@[inline] def empty : BinomialHeap α le := mkBinomialHeap α le

instance : EmptyCollection (BinomialHeap α le) := ⟨.empty⟩
instance : Inhabited (BinomialHeap α le) := ⟨.empty⟩

/-- `O(1)`. Is the heap empty? -/
@[inline] def isEmpty (b : BinomialHeap α le) : Bool := b.1.isEmpty

/-- `O(log n)`. The number of elements in the heap. -/
@[inline] def size (b : BinomialHeap α le) : Nat := b.1.size

/-- `O(1)`. Make a new heap containing `a`. -/
@[inline] def singleton (a : α) : BinomialHeap α le := ⟨Heap.singleton a, Heap.WF.singleton⟩

/-- `O(log n)`. Merge the contents of two heaps. -/
@[inline] def merge : BinomialHeap α le → BinomialHeap α le → BinomialHeap α le
  | ⟨b₁, h₁⟩, ⟨b₂, h₂⟩ => ⟨b₁.merge le b₂, h₁.merge h₂⟩

/-- `O(log n)`. Add element `a` to the given heap `h`. -/
@[inline] def insert (a : α) (h : BinomialHeap α le) : BinomialHeap α le := merge (singleton a) h

/-- `O(n log n)`. Construct a heap from a list by inserting all the elements. -/
def ofList (le : α → α → Bool) (as : List α) : BinomialHeap α le := as.foldl (flip insert) empty

/-- `O(n log n)`. Construct a heap from a list by inserting all the elements. -/
def ofArray (le : α → α → Bool) (as : Array α) : BinomialHeap α le := as.foldl (flip insert) empty

/-- `O(log n)`. Remove and return the minimum element from the heap. -/
@[inline] def deleteMin (b : BinomialHeap α le) : Option (α × BinomialHeap α le) :=
  match eq : b.1.deleteMin le with
  | none => none
  | some (a, tl) => some (a, ⟨tl, b.2.deleteMin eq⟩)

instance : Std.Stream (BinomialHeap α le) α := ⟨deleteMin⟩

/--
`O(n log n)`. Implementation of `for x in (b : BinomialHeap α le) ...` notation,
which iterates over the elements in the heap in increasing order.
-/
protected def forIn [Monad m] (b : BinomialHeap α le) (x : β) (f : α → β → m (ForInStep β)) : m β :=
  ForInStep.run <$> b.1.foldM le (.yield x) fun x a => x.bind (f a)

instance [Monad m] : ForIn m (BinomialHeap α le) α := ⟨BinomialHeap.forIn⟩

/-- `O(log n)`. Returns the smallest element in the heap, or `none` if the heap is empty. -/
@[inline] def head? (b : BinomialHeap α le) : Option α := b.1.head? le

/-- `O(log n)`. Returns the smallest element in the heap, or panics if the heap is empty. -/
@[inline] def head! [Inhabited α] (b : BinomialHeap α le) : α := b.head?.get!

/-- `O(log n)`. Returns the smallest element in the heap, or `default` if the heap is empty. -/
@[inline] def headI [Inhabited α] (b : BinomialHeap α le) : α := b.head?.getD default

/-- `O(log n)`. Removes the smallest element from the heap, or `none` if the heap is empty. -/
@[inline] def tail? (b : BinomialHeap α le) : Option (BinomialHeap α le) :=
  match eq : b.1.tail? le with
  | none => none
  | some tl => some ⟨tl, b.2.tail? eq⟩

/-- `O(log n)`. Removes the smallest element from the heap, if possible. -/
@[inline] def tail (b : BinomialHeap α le) : BinomialHeap α le := ⟨b.1.tail le, b.2.tail⟩

/--
`O(n log n)`. Monadic fold over the elements of a heap in increasing order,
by repeatedly pulling the minimum element out of the heap.
-/
@[inline] def foldM [Monad m] (b : BinomialHeap α le) (init : β) (f : β → α → m β) : m β :=
  b.1.foldM le init f

/--
`O(n log n)`. Fold over the elements of a heap in increasing order,
by repeatedly pulling the minimum element out of the heap.
-/
@[inline] def fold (b : BinomialHeap α le) (init : β) (f : β → α → β) : β := b.1.fold le init f

/-- `O(n log n)`. Convert the heap to a list in increasing order. -/
@[inline] def toList (b : BinomialHeap α le) : List α := b.1.toList le

/-- `O(n log n)`. Convert the heap to an array in increasing order. -/
@[inline] def toArray (b : BinomialHeap α le) : Array α := b.1.toArray le

/-- `O(n)`. Convert the heap to a list in arbitrary order. -/
@[inline] def toListUnordered (b : BinomialHeap α le) : List α := b.1.toListUnordered

/-- `O(n)`. Convert the heap to an array in arbitrary order. -/
@[inline] def toArrayUnordered (b : BinomialHeap α le) : Array α := b.1.toArrayUnordered

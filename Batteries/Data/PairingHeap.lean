/-
Copyright (c) 2022 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
import Batteries.Classes.Order

namespace Batteries.PairingHeapImp

/--
A `Heap` is the nodes of the pairing heap.
Each node have two pointers: `child` going to the first child of this node,
and `sibling` goes to the next sibling of this tree.
So it actually encodes a forest where each node has children
`node.child`, `node.child.sibling`, `node.child.sibling.sibling`, etc.

Each edge in this forest denotes a `le a b` relation that has been checked, so
the root is smaller than everything else under it.
-/
inductive Heap (α : Type u) where
  /-- An empty forest, which has depth `0`. -/
  | nil : Heap α
  /-- A forest consists of a root `a`, a forest `child` elements greater than `a`,
  and another forest `sibling`. -/
  | node (a : α) (child sibling : Heap α) : Heap α
  deriving Repr

/-- `O(n)`. The number of elements in the heap. -/
def Heap.size : Heap α → Nat
  | .nil => 0
  | .node _ c s => c.size + 1 + s.size

/-- A node containing a single element `a`. -/
def Heap.singleton (a : α) : Heap α := .node a .nil .nil

/-- `O(1)`. Is the heap empty? -/
def Heap.isEmpty : Heap α → Bool
  | .nil => true
  | _    => false

/-- `O(1)`. Merge two heaps. Ignore siblings. -/
@[specialize] def Heap.merge (le : α → α → Bool) : Heap α → Heap α → Heap α
  | .nil, .nil => .nil
  | .nil, .node a₂ c₂ _ => .node a₂ c₂ .nil
  | .node a₁ c₁ _, .nil => .node a₁ c₁ .nil
  | .node a₁ c₁ _, .node a₂ c₂ _ =>
    if le a₁ a₂ then .node a₁ (.node a₂ c₂ c₁) .nil else .node a₂ (.node a₁ c₁ c₂) .nil

/-- Auxiliary for `Heap.deleteMin`: merge the forest in pairs. -/
@[specialize] def Heap.combine (le : α → α → Bool) : Heap α → Heap α
  | h₁@(.node _ _ h₂@(.node _ _ s)) => merge le (merge le h₁ h₂) (s.combine le)
  | h => h

/-- `O(1)`. Get the smallest element in the heap, including the passed in value `a`. -/
@[inline] def Heap.headD (a : α) : Heap α → α
  | .nil => a
  | .node a _ _ => a

/-- `O(1)`. Get the smallest element in the heap, if it has an element. -/
@[inline] def Heap.head? : Heap α → Option α
  | .nil => none
  | .node a _ _ => some a

/-- Amortized `O(log n)`. Find and remove the the minimum element from the heap. -/
@[inline] def Heap.deleteMin (le : α → α → Bool) : Heap α → Option (α × Heap α)
  | .nil => none
  | .node a c _ => (a, combine le c)

/-- Amortized `O(log n)`. Get the tail of the pairing heap after removing the minimum element. -/
@[inline] def Heap.tail? (le : α → α → Bool) (h : Heap α) : Option (Heap α) :=
  deleteMin le h |>.map (·.snd)

/-- Amortized `O(log n)`. Remove the minimum element of the heap. -/
@[inline] def Heap.tail (le : α → α → Bool) (h : Heap α) : Heap α :=
  tail? le h |>.getD .nil

/-- A predicate says there is no more than one tree. -/
inductive Heap.NoSibling : Heap α → Prop
  /-- An empty heap is no more than one tree. -/
  | nil : NoSibling .nil
  /-- Or there is exactly one tree. -/
  | node (a c) : NoSibling (.node a c .nil)

instance : Decidable (Heap.NoSibling s) :=
  match s with
  | .nil => isTrue .nil
  | .node a c .nil => isTrue (.node a c)
  | .node _ _ (.node _ _ _) => isFalse nofun

theorem Heap.noSibling_merge (le) (s₁ s₂ : Heap α) :
    (s₁.merge le s₂).NoSibling := by
  unfold merge
  (split <;> try split) <;> constructor

theorem Heap.noSibling_combine (le) (s : Heap α) :
    (s.combine le).NoSibling := by
  unfold combine; split
  · exact noSibling_merge _ _ _
  · match s with
    | nil | node _ _ nil => constructor
    | node _ _ (node _ _ s) => rename_i h; exact (h _ _ _ _ _ rfl).elim

theorem Heap.noSibling_deleteMin {s : Heap α} (eq : s.deleteMin le = some (a, s')) :
    s'.NoSibling := by
  cases s with cases eq | node a c => exact noSibling_combine _ _

theorem Heap.noSibling_tail? {s : Heap α} : s.tail? le = some s' →
    s'.NoSibling := by
  simp only [Heap.tail?]; intro eq
  match eq₂ : s.deleteMin le, eq with
  | some (a, tl), rfl => exact noSibling_deleteMin eq₂

theorem Heap.noSibling_tail (le) (s : Heap α) : (s.tail le).NoSibling := by
  simp only [Heap.tail]
  match eq : s.tail? le with
  | none => cases s with cases eq | nil => constructor
  | some tl => exact Heap.noSibling_tail? eq

theorem Heap.size_merge_node (le) (a₁ : α) (c₁ s₁ : Heap α) (a₂ : α) (c₂ s₂ : Heap α) :
    (merge le (.node a₁ c₁ s₁) (.node a₂ c₂ s₂)).size = c₁.size + c₂.size + 2 := by
  unfold merge; dsimp; split <;> simp_arith [size]

theorem Heap.size_merge (le) {s₁ s₂ : Heap α} (h₁ : s₁.NoSibling) (h₂ : s₂.NoSibling) :
    (merge le s₁ s₂).size = s₁.size + s₂.size := by
  match h₁, h₂ with
  | .nil, .nil | .nil, .node _ _ | .node _ _, .nil => simp [size]
  | .node _ _, .node _ _ => unfold merge; dsimp; split <;> simp_arith [size]

theorem Heap.size_combine (le) (s : Heap α) :
    (s.combine le).size = s.size := by
  unfold combine; split
  · rename_i a₁ c₁ a₂ c₂ s
    rw [size_merge le (noSibling_merge _ _ _) (noSibling_combine _ _),
      size_merge_node, size_combine le s]
    simp_arith [size]
  · rfl

theorem Heap.size_deleteMin {s : Heap α} (h : s.NoSibling) (eq : s.deleteMin le = some (a, s')) :
    s.size = s'.size + 1 := by
  cases h with cases eq | node a c => rw [size_combine, size, size]

theorem Heap.size_tail? {s : Heap α} (h : s.NoSibling) : s.tail? le = some s' →
    s.size = s'.size + 1 := by
  simp only [Heap.tail?]; intro eq
  match eq₂ : s.deleteMin le, eq with
  | some (a, tl), rfl => exact size_deleteMin h eq₂

theorem Heap.size_tail (le) {s : Heap α} (h : s.NoSibling) : (s.tail le).size = s.size - 1 := by
  simp only [Heap.tail]
  match eq : s.tail? le with
  | none => cases s with cases eq | nil => rfl
  | some tl => simp [Heap.size_tail? h eq]

theorem Heap.size_deleteMin_lt {s : Heap α} (eq : s.deleteMin le = some (a, s')) :
    s'.size < s.size := by
  cases s with cases eq | node a c => simp_arith [size_combine, size]

theorem Heap.size_tail?_lt {s : Heap α} : s.tail? le = some s' →
    s'.size < s.size := by
  simp only [Heap.tail?]; intro eq
  match eq₂ : s.deleteMin le, eq with
  | some (a, tl), rfl => exact size_deleteMin_lt eq₂

/--
`O(n log n)`. Monadic fold over the elements of a heap in increasing order,
by repeatedly pulling the minimum element out of the heap.
-/
@[specialize] def Heap.foldM [Monad m] (le : α → α → Bool) (s : Heap α)
    (init : β) (f : β → α → m β) : m β :=
  match eq : s.deleteMin le with
  | none => pure init
  | some (hd, tl) =>
    have : tl.size < s.size := by simp_arith [Heap.size_deleteMin_lt eq]
    do foldM le tl (← f init hd) f
termination_by s.size

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

/-- `O(n)`. Fold a monadic function over the tree structure to accumulate a value. -/
@[specialize] def Heap.foldTreeM [Monad m] (nil : β) (join : α → β → β → m β) : Heap α → m β
  | .nil => pure nil
  | .node a c s => do join a (← c.foldTreeM nil join) (← s.foldTreeM nil join)

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
-/
def Heap.NodeWF (le : α → α → Bool) (a : α) : Heap α → Prop
  | .nil => True
  | .node b c s => (∀ [TotalBLE le], le a b) ∧ c.NodeWF le b ∧ s.NodeWF le a

/--
The well formedness predicate for a pairing heap.
It asserts that:
* There is no more than one tree.
* It is a `le`-min-heap (if `le` is well-behaved)
-/
inductive Heap.WF (le : α → α → Bool) : Heap α → Prop
  /-- It is an empty heap. -/
  | nil : WF le .nil
  /-- There is exactly one tree and it is a `le`-min-heap. -/
  | node (h : c.NodeWF le a) : WF le (.node a c .nil)

theorem Heap.WF.singleton : (Heap.singleton a).WF le := node trivial

theorem Heap.WF.merge_node (h₁ : NodeWF le a₁ c₁) (h₂ : NodeWF le a₂ c₂) :
    (merge le (.node a₁ c₁ s₁) (.node a₂ c₂ s₂)).WF le := by
  unfold merge; dsimp
  split <;> rename_i h
  · exact node ⟨fun [_] => h, h₂, h₁⟩
  · exact node ⟨fun [_] => TotalBLE.total.resolve_left h, h₁, h₂⟩

theorem Heap.WF.merge (h₁ : s₁.WF le) (h₂ : s₂.WF le) :
    (merge le s₁ s₂).WF le :=
  match h₁, h₂ with
  | .nil, .nil => nil
  | .nil, .node h₂ => node h₂
  | .node h₁, .nil => node h₁
  | .node h₁, .node h₂ => merge_node h₁ h₂

theorem Heap.WF.combine (h : s.NodeWF le a) : (combine le s).WF le :=
  match s with
  | .nil => nil
  | .node _b _c .nil => node h.2.1
  | .node _b₁ _c₁ (.node _b₂ _c₂ _s) => merge (merge_node h.2.1 h.2.2.2.1) (combine h.2.2.2.2)

theorem Heap.WF.deleteMin {s : Heap α} (h : s.WF le)
    (eq : s.deleteMin le = some (a, s')) : s'.WF le := by
  cases h with cases eq | node h => exact Heap.WF.combine h

theorem Heap.WF.tail? (hwf : (s : Heap α).WF le) : s.tail? le = some tl →
  tl.WF le := by
  simp only [Heap.tail?]; intro eq
  match eq₂ : s.deleteMin le, eq with
  | some (a, tl), rfl => exact hwf.deleteMin eq₂

theorem Heap.WF.tail (hwf : (s : Heap α).WF le) : (s.tail le).WF le := by
  simp only [Heap.tail]
  match eq : s.tail? le with
  | none => exact Heap.WF.nil
  | some tl => exact hwf.tail? eq

theorem Heap.deleteMin_fst : ((s : Heap α).deleteMin le).map (·.1) = s.head? :=
  match s with
  | .nil => rfl
  | .node _ _ _ => rfl

end PairingHeapImp

open PairingHeapImp

/--
A [pairing heap](https://en.wikipedia.org/wiki/Pairing_heap) is a data structure which supports
the following primary operations:

* `insert : α → PairingHeap α → PairingHeap α`: add an element to the heap
* `deleteMin : PairingHeap α → Option (α × PairingHeap α)`:
  remove the minimum element from the heap
* `merge : PairingHeap α → PairingHeap α → PairingHeap α`: combine two heaps

The first two operations are known as a "priority queue", so this could be called
a "mergeable priority queue". The standard choice for a priority queue is a binary heap,
which supports `insert` and `deleteMin` in `O(log n)`, but `merge` is `O(n)`.
With a `PairingHeap`, `insert` and `merge` are `O(1)`, `deleteMin` is amortized `O(log n)`.

Note that `deleteMin` may be `O(n)` in a single operation. So if you need an efficient
persistent priority queue, you should use other data structures with better worst-case time.
-/
def PairingHeap (α : Type u) (le : α → α → Bool) :=
  { h : Heap α // h.WF le }

/-- `O(1)`. Make a new empty pairing heap. -/
@[inline] def mkPairingHeap (α : Type u) (le : α → α → Bool) : PairingHeap α le :=
  ⟨.nil, Heap.WF.nil⟩

namespace PairingHeap
variable {α : Type u} {le : α → α → Bool}

/-- `O(1)`. Make a new empty pairing heap. -/
@[inline] def empty : PairingHeap α le := mkPairingHeap α le

instance : Inhabited (PairingHeap α le) := ⟨.empty⟩

/-- `O(1)`. Is the heap empty? -/
@[inline] def isEmpty (b : PairingHeap α le) : Bool := b.1.isEmpty

/-- `O(n)`. The number of elements in the heap. -/
@[inline] def size (b : PairingHeap α le) : Nat := b.1.size

/-- `O(1)`. Make a new heap containing `a`. -/
@[inline] def singleton (a : α) : PairingHeap α le :=
  ⟨Heap.singleton a, Heap.WF.singleton⟩

/-- `O(1)`. Merge the contents of two heaps. -/
@[inline] def merge : PairingHeap α le → PairingHeap α le → PairingHeap α le
  | ⟨b₁, h₁⟩, ⟨b₂, h₂⟩ => ⟨b₁.merge le b₂, h₁.merge h₂⟩

/-- `O(1)`. Add element `a` to the given heap `h`. -/
@[inline] def insert (a : α) (h : PairingHeap α le) : PairingHeap α le :=
  merge (singleton a) h

/-- `O(n log n)`. Construct a heap from a list by inserting all the elements. -/
def ofList (le : α → α → Bool) (as : List α) : PairingHeap α le :=
  as.foldl (flip insert) empty

/-- `O(n log n)`. Construct a heap from a list by inserting all the elements. -/
def ofArray (le : α → α → Bool) (as : Array α) : PairingHeap α le :=
  as.foldl (flip insert) empty

/-- Amortized `O(log n)`. Remove and return the minimum element from the heap. -/
@[inline] def deleteMin (b : PairingHeap α le) : Option (α × PairingHeap α le) :=
  match eq : b.1.deleteMin le with
  | none => none
  | some (a, tl) => some (a, ⟨tl, b.2.deleteMin eq⟩)

/-- `O(1)`. Returns the smallest element in the heap, or `none` if the heap is empty. -/
@[inline] def head? (b : PairingHeap α le) : Option α := b.1.head?

/-- `O(1)`. Returns the smallest element in the heap, or panics if the heap is empty. -/
@[inline] def head! [Inhabited α] (b : PairingHeap α le) : α := b.head?.get!

/-- `O(1)`. Returns the smallest element in the heap, or `default` if the heap is empty. -/
@[inline] def headI [Inhabited α] (b : PairingHeap α le) : α := b.head?.getD default

/--
Amortized `O(log n)`. Removes the smallest element from the heap, or `none` if the heap is empty.
-/
@[inline] def tail? (b : PairingHeap α le) : Option (PairingHeap α le) :=
  match eq : b.1.tail? le with
  | none => none
  | some tl => some ⟨tl, b.2.tail? eq⟩

/-- Amortized `O(log n)`. Removes the smallest element from the heap, if possible. -/
@[inline] def tail (b : PairingHeap α le) : PairingHeap α le := ⟨b.1.tail le, b.2.tail⟩

/-- `O(n log n)`. Convert the heap to a list in increasing order. -/
@[inline] def toList (b : PairingHeap α le) : List α := b.1.toList le

/-- `O(n log n)`. Convert the heap to an array in increasing order. -/
@[inline] def toArray (b : PairingHeap α le) : Array α := b.1.toArray le

/-- `O(n)`. Convert the heap to a list in arbitrary order. -/
@[inline] def toListUnordered (b : PairingHeap α le) : List α := b.1.toListUnordered

/-- `O(n)`. Convert the heap to an array in arbitrary order. -/
@[inline] def toArrayUnordered (b : PairingHeap α le) : Array α := b.1.toArrayUnordered

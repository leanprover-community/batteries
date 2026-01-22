/-
Copyright (c) 2021 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, François G. Dorais
-/
module

public section

namespace Batteries

/-- A max-heap data structure. -/
structure BinaryHeap (α: Type w) where
  /-- `O(1)`. Get data array for a `BinaryHeap`. -/
  arr : Array α

namespace BinaryHeap
variable {α : Type w}


/-- Given a node, return the index of its larger child, if it exists -/
def maxChild [Ord α] (a : Vector α sz) (i : Fin sz) : Option (Fin sz) :=
  let left := 2 * i.1 + 1
  let right := left + 1
  if hleft : left < sz then
    if hright : right < sz then
      if compare a[left] a[right] |>.isLT then
        some ⟨right, hright⟩
      else
        some ⟨left, hleft⟩
    else
      some ⟨left, hleft⟩
  else none

/-- Core operation for binary heaps, expressed directly on arrays.
Given an array which is a max-heap, push item `i` down to restore the max-heap property. -/
@[expose]
def heapifyDown [Ord α] (a : Vector α sz) (i : Fin sz) :
    Vector α sz :=
  match h : maxChild a i with
  | none => a
  | some j =>
    have : i < j := by grind [maxChild]
    if compare a[i] a[j] |>.isLT then
      heapifyDown (a.swap i j) j
    else a
termination_by sz - i

/-- Core operation for binary heaps, expressed directly on arrays.
Construct a heap from an unsorted array, by heapifying all the elements. -/
@[inline]
def mkHeap [Ord α] (a : Vector α sz) : Vector α sz :=
  loop (sz / 2) a (Nat.div_le_self ..)
where
  /-- Inner loop for `mkHeap`. -/
  loop : (i : Nat) → (a : Vector α sz) → i ≤ sz → Vector α sz
  | 0, a, _ => a
  | i+1, a, h =>
    let a' := heapifyDown a ⟨i, Nat.lt_of_succ_le h⟩
    loop i a' (Nat.le_trans (Nat.le_succ _) h)

/-- Core operation for binary heaps, expressed directly on arrays.
Given an array which is a max-heap, push item `i` up to restore the max-heap property. -/
@[expose]
def heapifyUp [Ord α] (a : Vector α sz) (i : Fin sz) :
    Vector α sz :=
  match i with
  | ⟨0, _⟩ => a
  | ⟨i'+1, hi⟩ =>
    let j := i'/2
    if compare a[j] a[i] |>.isLT then
      heapifyUp (a.swap i j) ⟨j, by get_elem_tactic⟩
    else a

/-- `O(1)`. Build a new empty heap. -/
def empty : BinaryHeap α := ⟨#[]⟩

instance : Inhabited (BinaryHeap α) := ⟨empty⟩
instance : EmptyCollection (BinaryHeap α) := ⟨empty⟩
instance : Membership α (BinaryHeap α) where
  mem h x := x ∈ h.arr

theorem mem_def {x : α} {h : BinaryHeap α} : x ∈ h ↔ x ∈ h.arr := Iff.rfl

/-- `O(1)`. Build a one-element heap. -/
def singleton (x : α) : BinaryHeap α := ⟨#[x]⟩

/-- `O(1)`. Get the number of elements in a `BinaryHeap`. -/
@[expose]
def size (self : BinaryHeap α) : Nat := self.1.size

/-- `O(1)`. Get data vector of a `BinaryHeap`. -/
@[expose]
def vector (self : BinaryHeap α) : Vector α self.size := ⟨self.1, rfl⟩

/-- `O(1)`. Get an element in the heap by index. -/
def get (self : BinaryHeap α) (i : Fin self.size) : α := self.1[i]'(i.2)

/-- `O(log n)`. Insert an element into a `BinaryHeap`, preserving the max-heap property. -/
def insert [Ord α] (self : BinaryHeap α) (x : α) : BinaryHeap α where
  arr := heapifyUp (self.vector.push x) ⟨_, Nat.lt_succ_self _⟩ |>.toArray

/-- `O(1)`. Get the maximum element in a `BinaryHeap`. -/
def max (self : BinaryHeap α) : Option α := self.1[0]?

/-- `O(log n)`. Remove the maximum element from a `BinaryHeap`
Call `max` first to actually retrieve the maximum element. -/
@[expose]
def popMax [Ord α] (self : BinaryHeap α) : BinaryHeap α :=
  if h0 : self.size = 0 then self else
    have hs : self.size - 1 < self.size := Nat.pred_lt h0
    have h0 : 0 < self.size := Nat.zero_lt_of_ne_zero h0
    let v := self.vector.swap _ _ h0 hs |>.pop
    if h : 0 < self.size - 1 then
      ⟨heapifyDown v ⟨0, h⟩ |>.toArray⟩
    else
      ⟨v.toArray⟩

@[simp] theorem size_popMax [Ord α] (self : BinaryHeap α) :
    self.popMax.size = self.size - 1 := by
  simp only [popMax, size]
  split
  · simp [*]
  · split <;> simp

/-- `O(log n)`. Return and remove the maximum element from a `BinaryHeap`. -/
def extractMax [Ord α] (self : BinaryHeap α) : Option α × BinaryHeap α :=
  (self.max, self.popMax)


@[simp]
public theorem max_eq_none_iff {heap : BinaryHeap α} : heap.max = none ↔ heap.size = 0 := by
  simp [max, size]

theorem size_pos_of_max {self : BinaryHeap α} (h : self.max = some x) : 0 < self.size := by
  simp only [max, getElem?_def] at h
  split at h
  · assumption
  · contradiction

/-- `O(log n)`. Equivalent to `extractMax (self.insert x)`, except that extraction cannot fail. -/
def insertExtractMax [Ord α] (self : BinaryHeap α) (x : α) : α × BinaryHeap α :=
  match e : self.max with
  | none => (x, self)
  | some m =>
    if compare x m |>.isLT then
      let v := self.vector.set 0 x (size_pos_of_max e)
      (m, ⟨heapifyDown v ⟨0, size_pos_of_max e⟩ |>.toArray⟩)
    else (x, self)

/-- `O(log n)`. Equivalent to `(self.max, self.popMax.insert x)`. -/
def replaceMax [Ord α] (self : BinaryHeap α) (x : α) : Option α × BinaryHeap α :=
  match e : self.max with
  | none => (none, ⟨self.vector.push x |>.toArray⟩)
  | some m =>
    let v := self.vector.set 0 x (size_pos_of_max e)
    (some m, ⟨heapifyDown v ⟨0, size_pos_of_max e⟩ |>.toArray⟩)

/-- `O(log n)`. Replace the value at index `i` by `x`. Assumes that `x ≤ self.get i`. -/
def decreaseKey [Ord α] (self : BinaryHeap α) (i : Fin self.size) (x : α) : BinaryHeap α where
  arr := heapifyDown (self.vector.set i x) i |>.toArray

/-- `O(log n)`. Replace the value at index `i` by `x`. Assumes that `self.get i ≤ x`. -/
def increaseKey [Ord α] (self : BinaryHeap α) (i : Fin self.size) (x : α) : BinaryHeap α where
  arr := heapifyUp (self.vector.set i x) i |>.toArray

end Batteries.BinaryHeap

/-- `O(n)`. Convert an unsorted vector to a `BinaryHeap`. -/
def Batteries.Vector.toBinaryHeap [Ord α] (v : Vector α n) :
    Batteries.BinaryHeap α where
  arr := BinaryHeap.mkHeap v |>.toArray

open Batteries in
/-- `O(n)`. Convert an unsorted array to a `BinaryHeap`. -/
def Array.toBinaryHeap [instOrd : Ord α] (a : Array α) : Batteries.BinaryHeap α where
  arr := BinaryHeap.mkHeap ⟨a, rfl⟩ |>.toArray

open Batteries in

/-- `O(n log n)`. Sort an array using a `BinaryHeap`. -/
@[inline, specialize]
def Array.heapSort [instOrd : Ord α] (a : Array α) : Array α :=
  loop (instOrd := instOrd.opposite) (a.toBinaryHeap (instOrd := instOrd.opposite)) #[]
where
  /-- Inner loop for `heapSort`. -/
  loop [instOrd : Ord α] (a : Batteries.BinaryHeap α) (out : Array α) : Array α :=
    match e: a.max with
    | none => out
    | some x =>
      have : a.popMax.size < a.size := by
        simp; exact Nat.sub_lt (Batteries.BinaryHeap.size_pos_of_max e) Nat.zero_lt_one
      loop a.popMax (out.push x)
  termination_by a.size

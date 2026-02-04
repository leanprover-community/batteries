/-
Copyright (c) 2021 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, François G. Dorais, Chad Sharp
-/
module

public section

namespace Batteries

/-- A max-heap data structure. -/
structure BinaryHeap (α : Type w) [Ord α] where
  /-- `O(1)`. Get data array for a `BinaryHeap`. -/
  arr : Array α

namespace BinaryHeap
variable {α : Type w}

/-- Given a node, return the index of its larger child, if it exists -/
@[inline]
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

/-- maxChild returns an index greater than i. -/
theorem maxChild_gt [Ord α] {a : Vector α sz} {i : Fin sz} {j : Fin sz}
    (h : maxChild a i = some j) : i < j := by
  grind only [maxChild, Lean.Grind.toInt_fin]

/-- Core operation for binary heaps, expressed directly on arrays.
Given an array which is a max-heap, push item `i` down to restore the max-heap property. -/
@[expose, specialize]
def heapifyDown [Ord α] (a : Vector α sz) (i : Fin sz) :
    Vector α sz :=
  match h : maxChild a i with
  | none => a
  | some j =>
    have : i < j := maxChild_gt h
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
  @[specialize]
  loop : (i : Nat) → (a : Vector α sz) → i ≤ sz → Vector α sz
  | 0, a, _ => a
  | i+1, a, h =>
    let a' := heapifyDown a ⟨i, Nat.lt_of_succ_le h⟩
    loop i a' (Nat.le_trans (Nat.le_succ _) h)

/-- Core operation for binary heaps, expressed directly on arrays.
Given an array which is a max-heap, push item `i` up to restore the max-heap property. -/
@[specialize]
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
@[inline]
def empty [Ord α] : BinaryHeap α := ⟨#[]⟩

instance [Ord α] : Inhabited (BinaryHeap α) := ⟨empty⟩
instance [Ord α] : EmptyCollection (BinaryHeap α) := ⟨empty⟩
instance [Ord α] : Membership α (BinaryHeap α) where
  mem h x := x ∈ h.arr

theorem mem_def [Ord α] {x : α} {h : BinaryHeap α} : x ∈ h ↔ x ∈ h.arr := Iff.rfl

/-- `O(1)`. Build a one-element heap. -/
@[inline]
def singleton [Ord α] (x : α) : BinaryHeap α := ⟨#[x]⟩

/-- `O(1)`. Get the number of elements in a `BinaryHeap`. -/
@[inline]
def size [Ord α] (self : BinaryHeap α) : Nat := self.arr.size

/-- `O(1)`. Get data vector of a `BinaryHeap`. -/
@[inline]
def vector [Ord α] (self : BinaryHeap α) : Vector α self.size := ⟨self.arr, rfl⟩

/-- `O(1)`. Get an element in the heap by index. -/
@[inline]
def get [Ord α] (self : BinaryHeap α) (i : Fin self.size) : α := self.arr[i]'(i.2)

/-- `O(log n)`. Insert an element into a `BinaryHeap`, preserving the max-heap property. -/
@[inline]
def insert [Ord α] (self : BinaryHeap α) (x : α) : BinaryHeap α where
  arr := heapifyUp (self.vector.push x) ⟨_, Nat.lt_succ_self _⟩ |>.toArray

/-- `O(1)`. Get the maximum element in a `BinaryHeap`. -/
@[inline]
def max [Ord α] (self : BinaryHeap α) : Option α := self.arr[0]?

/-- `O(log n)`. Remove the maximum element from a `BinaryHeap`
Call `max` first to actually retrieve the maximum element. -/
@[inline]
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
@[inline]
def extractMax [Ord α] (self : BinaryHeap α) : Option α × BinaryHeap α :=
  (self.max, self.popMax)

@[simp]
theorem max_eq_none_iff [Ord α] {heap : BinaryHeap α} :
    heap.max = none ↔ heap.size = 0 := by
  simp [max, size]

theorem size_pos_of_max [Ord α] {self : BinaryHeap α} (h : self.max = some x) : 0 < self.size := by
  simp only [max, getElem?_def] at h
  split at h
  · assumption
  · contradiction

/-- `O(log n)`. Equivalent to `extractMax (self.insert x)`, except that extraction cannot fail. -/
@[inline]
def insertExtractMax [Ord α] (self : BinaryHeap α) (x : α) : α × BinaryHeap α :=
  match e : self.max with
  | none => (x, self)
  | some m =>
    if compare x m |>.isLT then
      let v := self.vector.set 0 x (size_pos_of_max e)
      (m, ⟨heapifyDown v ⟨0, size_pos_of_max e⟩ |>.toArray⟩)
    else (x, self)

/-- `O(log n)`. Equivalent to `(self.max, self.popMax.insert x)`. -/
@[inline]
def replaceMax [Ord α] (self : BinaryHeap α) (x : α) : Option α × BinaryHeap α :=
  match e : self.max with
  | none => (none, ⟨self.vector.push x |>.toArray⟩)
  | some m =>
    let v := self.vector.set 0 x (size_pos_of_max e)
    (some m, ⟨heapifyDown v ⟨0, size_pos_of_max e⟩ |>.toArray⟩)

/-- `O(log n)`. Replace the value at index `i` by `x`. Assumes that `x ≤ self.get i`. -/
@[inline]
def decreaseKey [Ord α] (self : BinaryHeap α) (i : Fin self.size) (x : α) : BinaryHeap α where
  arr := heapifyDown (self.vector.set i x) i |>.toArray

/-- `O(log n)`. Replace the value at index `i` by `x`. Assumes that `self.get i ≤ x`. -/
@[inline]
def increaseKey [Ord α] (self : BinaryHeap α) (i : Fin self.size) (x : α) : BinaryHeap α where
  arr := heapifyUp (self.vector.set i x) i |>.toArray

/-- `O(n log n)`. Return the contents of `self` as a sorted array -/
@[inline]
def toSortedArray [Ord α] (self : BinaryHeap α) : Array α :=
  loop self #[]
where
  @[specialize]
  loop [Ord α] (a : BinaryHeap α) (out : Array α) : Array α :=
    match _: a.max with
    | none => out
    | some x => loop a.popMax (out.push x)
  termination_by a.size
  decreasing_by
    have := size_pos_of_max ‹_›
    simp only [size_popMax]
    omega
end Batteries.BinaryHeap

/-- `O(n)`. Convert an unsorted vector to a `BinaryHeap`. -/
@[inline]
def Batteries.Vector.toBinaryHeap [Ord α] (v : Vector α n) :
    Batteries.BinaryHeap α where
  arr := BinaryHeap.mkHeap v |>.toArray

open Batteries in
/-- `O(n)`. Convert an unsorted array to a `BinaryHeap`. -/
@[inline]
def Array.toBinaryHeap [Ord α] (a : Array α) : Batteries.BinaryHeap α where
  arr := BinaryHeap.mkHeap ⟨a, rfl⟩ |>.toArray

/-- `O(n log n)`. Sort an array using a `BinaryHeap`. -/
@[inline]
def Array.heapSort [instOrd : Ord α] (a : Array α) : Array α :=
  letI := instOrd.opposite
  a.toBinaryHeap.toSortedArray

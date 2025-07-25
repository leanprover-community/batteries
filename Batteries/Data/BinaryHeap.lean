/-
Copyright (c) 2021 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, François G. Dorais
-/

import Batteries.Data.Vector.Basic

namespace Batteries

/-- A max-heap data structure. -/
structure BinaryHeap (α) (lt : α → α → Bool) where
  /-- `O(1)`. Get data array for a `BinaryHeap`. -/
  arr : Array α

namespace BinaryHeap

private def maxChild (lt : α → α → Bool) (a : Vector α sz) (i : Fin sz) : Option (Fin sz) :=
  let left := 2 * i.1 + 1
  let right := left + 1
  if hleft : left < sz then
    if hright : right < sz then
      if lt a[left] a[right] then
        some ⟨right, hright⟩
      else
        some ⟨left, hleft⟩
    else
      some ⟨left, hleft⟩
  else none

/-- Core operation for binary heaps, expressed directly on arrays.
Given an array which is a max-heap, push item `i` down to restore the max-heap property. -/
def heapifyDown (lt : α → α → Bool) (a : Vector α sz) (i : Fin sz) :
    Vector α sz :=
  match h : maxChild lt a i with
  | none => a
  | some j =>
    have : i < j := by
      cases i; cases j
      simp only [maxChild] at h
      split at h
      · split at h
        · split at h <;> (cases h; simp +arith)
        · cases h; simp +arith
      · contradiction
    if lt a[i] a[j] then
      heapifyDown lt (a.swap i j) j
    else a
termination_by sz - i

/-- Core operation for binary heaps, expressed directly on arrays.
Construct a heap from an unsorted array, by heapifying all the elements. -/
def mkHeap (lt : α → α → Bool) (a : Vector α sz) : Vector α sz :=
  loop (sz / 2) a (Nat.div_le_self ..)
where
  /-- Inner loop for `mkHeap`. -/
  loop : (i : Nat) → (a : Vector α sz) → i ≤ sz → Vector α sz
  | 0, a, _ => a
  | i+1, a, h =>
    let a' := heapifyDown lt a ⟨i, Nat.lt_of_succ_le h⟩
    loop i a' (Nat.le_trans (Nat.le_succ _) h)

/-- Core operation for binary heaps, expressed directly on arrays.
Given an array which is a max-heap, push item `i` up to restore the max-heap property. -/
def heapifyUp (lt : α → α → Bool) (a : Vector α sz) (i : Fin sz) :
    Vector α sz :=
  match i with
  | ⟨0, _⟩ => a
  | ⟨i'+1, hi⟩ =>
    let j := i'/2
    if lt a[j] a[i] then
      heapifyUp lt (a.swap i j) ⟨j, by get_elem_tactic⟩
    else a

/-- `O(1)`. Build a new empty heap. -/
def empty (lt) : BinaryHeap α lt := ⟨#[]⟩

instance (lt) : Inhabited (BinaryHeap α lt) := ⟨empty _⟩
instance (lt) : EmptyCollection (BinaryHeap α lt) := ⟨empty _⟩

/-- `O(1)`. Build a one-element heap. -/
def singleton (lt) (x : α) : BinaryHeap α lt := ⟨#[x]⟩

/-- `O(1)`. Get the number of elements in a `BinaryHeap`. -/
def size (self : BinaryHeap α lt) : Nat := self.1.size

/-- `O(1)`. Get data vector of a `BinaryHeap`. -/
def vector (self : BinaryHeap α lt) : Vector α self.size := ⟨self.1, rfl⟩

/-- `O(1)`. Get an element in the heap by index. -/
def get (self : BinaryHeap α lt) (i : Fin self.size) : α := self.1[i]'(i.2)

/-- `O(log n)`. Insert an element into a `BinaryHeap`, preserving the max-heap property. -/
def insert (self : BinaryHeap α lt) (x : α) : BinaryHeap α lt where
  arr := heapifyUp lt (self.vector.push x) ⟨_, Nat.lt_succ_self _⟩ |>.toArray

@[simp] theorem size_insert (self : BinaryHeap α lt) (x : α) :
    (self.insert x).size = self.size + 1 := by
  simp [size, insert]

/-- `O(1)`. Get the maximum element in a `BinaryHeap`. -/
def max (self : BinaryHeap α lt) : Option α := self.1[0]?

/-- `O(log n)`. Remove the maximum element from a `BinaryHeap`.
Call `max` first to actually retrieve the maximum element. -/
def popMax (self : BinaryHeap α lt) : BinaryHeap α lt :=
  if h0 : self.size = 0 then self else
    have hs : self.size - 1 < self.size := Nat.pred_lt h0
    have h0 : 0 < self.size := Nat.zero_lt_of_ne_zero h0
    let v := self.vector.swap _ _ h0 hs |>.pop
    if h : 0 < self.size - 1 then
      ⟨heapifyDown lt v ⟨0, h⟩ |>.toArray⟩
    else
      ⟨v.toArray⟩

@[simp] theorem size_popMax (self : BinaryHeap α lt) :
    self.popMax.size = self.size - 1 := by
  simp only [popMax, size]
  split
  · simp +arith [*]
  · split <;> simp +arith

/-- `O(log n)`. Return and remove the maximum element from a `BinaryHeap`. -/
def extractMax (self : BinaryHeap α lt) : Option α × BinaryHeap α lt :=
  (self.max, self.popMax)

theorem size_pos_of_max {self : BinaryHeap α lt} (h : self.max = some x) : 0 < self.size := by
  simp only [max, getElem?_def] at h
  split at h
  · assumption
  · contradiction

/-- `O(log n)`. Equivalent to `extractMax (self.insert x)`, except that extraction cannot fail. -/
def insertExtractMax (self : BinaryHeap α lt) (x : α) : α × BinaryHeap α lt :=
  match e : self.max with
  | none => (x, self)
  | some m =>
    if lt x m then
      let v := self.vector.set 0 x (size_pos_of_max e)
      (m, ⟨heapifyDown lt v ⟨0, size_pos_of_max e⟩ |>.toArray⟩)
    else (x, self)

/-- `O(log n)`. Equivalent to `(self.max, self.popMax.insert x)`. -/
def replaceMax (self : BinaryHeap α lt) (x : α) : Option α × BinaryHeap α lt :=
  match e : self.max with
  | none => (none, ⟨self.vector.push x |>.toArray⟩)
  | some m =>
    let v := self.vector.set 0 x (size_pos_of_max e)
    (some m, ⟨heapifyDown lt v ⟨0, size_pos_of_max e⟩ |>.toArray⟩)

/-- `O(log n)`. Replace the value at index `i` by `x`. Assumes that `x ≤ self.get i`. -/
def decreaseKey (self : BinaryHeap α lt) (i : Fin self.size) (x : α) : BinaryHeap α lt where
  arr := heapifyDown lt (self.vector.set i x) i |>.toArray

/-- `O(log n)`. Replace the value at index `i` by `x`. Assumes that `self.get i ≤ x`. -/
def increaseKey (self : BinaryHeap α lt) (i : Fin self.size) (x : α) : BinaryHeap α lt where
  arr := heapifyUp lt (self.vector.set i x) i |>.toArray

end Batteries.BinaryHeap

/-- `O(n)`. Convert an unsorted vector to a `BinaryHeap`. -/
def Batteries.Vector.toBinaryHeap (lt : α → α → Bool) (v : Vector α n) :
    Batteries.BinaryHeap α lt where
  arr := BinaryHeap.mkHeap lt v |>.toArray

open Batteries in
/-- `O(n)`. Convert an unsorted array to a `BinaryHeap`. -/
def Array.toBinaryHeap (lt : α → α → Bool) (a : Array α) : Batteries.BinaryHeap α lt where
  arr := BinaryHeap.mkHeap lt ⟨a, rfl⟩ |>.toArray

open Batteries in
/-- `O(n log n)`. Sort an array using a `BinaryHeap`. -/
@[specialize] def Array.heapSort (a : Array α) (lt : α → α → Bool) : Array α :=
  loop (a.toBinaryHeap (flip lt)) #[]
where
  /-- Inner loop for `heapSort`. -/
  loop (a : Batteries.BinaryHeap α (flip lt)) (out : Array α) : Array α :=
    match e: a.max with
    | none => out
    | some x =>
      have : a.popMax.size < a.size := by
        simp; exact Nat.sub_lt (Batteries.BinaryHeap.size_pos_of_max e) Nat.zero_lt_one
      loop a.popMax (out.push x)
  termination_by a.size

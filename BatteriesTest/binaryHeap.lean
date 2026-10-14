import Batteries.Data.BinaryHeap

open Batteries

/-! ### `heapSort` -/

#guard (#[] : Array Nat).heapSort == #[]
#guard #[1].heapSort == #[1]
#guard #[3, 1, 2, 5, 4].heapSort == #[1, 2, 3, 4, 5]
#guard #[2, 2, 1, 3, 1].heapSort == #[1, 1, 2, 2, 3]
#guard #[5, 4, 3, 2, 1].heapSort == #[1, 2, 3, 4, 5]
#guard #["pear", "apple", "fig"].heapSort == #["apple", "fig", "pear"]

/-- A deterministic pseudo-random array of length `n`. -/
def pseudoRandom (n : Nat) : Array Nat := Id.run do
  let mut out := #[]
  let mut x := 12345
  for _ in [0:n] do
    x := (x * 1103515245 + 12345) % 2147483648
    out := out.push (x % 1000)
  return out

#guard (pseudoRandom 500).heapSort == (pseudoRandom 500).qsort (· < ·)

-- `heapSort` with the opposite order sorts in descending order.
#guard (letI := (inferInstance : Ord Nat).opposite; #[3, 1, 2].heapSort) == #[3, 2, 1]

/-! ### Basic heap operations -/

#guard (BinaryHeap.empty : BinaryHeap Nat).max == none
#guard (BinaryHeap.empty : BinaryHeap Nat).size == 0
#guard (BinaryHeap.singleton 7).max == some 7
#guard (#[3, 1, 4, 1, 5].toBinaryHeap).max == some 5
#guard (#[3, 1, 4, 1, 5].toBinaryHeap).size == 5
#guard (#[3, 1, 4, 1, 5].toBinaryHeap).toSortedArray == #[5, 4, 3, 1, 1]
#guard (#v[3, 1, 2].toBinaryHeap).toSortedArray == #[3, 2, 1]

#guard ((#[3, 1, 4].toBinaryHeap).insert 9).max == some 9
#guard ((#[3, 1, 4].toBinaryHeap).insert 2).toSortedArray == #[4, 3, 2, 1]
#guard ([5, 3, 8, 1].foldl (·.insert ·) (BinaryHeap.empty : BinaryHeap Nat)).toSortedArray ==
  #[8, 5, 3, 1]

#guard (#[3, 1, 4].toBinaryHeap).popMax.toSortedArray == #[3, 1]
#guard (BinaryHeap.empty : BinaryHeap Nat).popMax.size == 0
#guard ((#[3, 1, 4].toBinaryHeap).extractMax.1) == some 4
#guard ((#[3, 1, 4].toBinaryHeap).extractMax.2.toSortedArray) == #[3, 1]

/-! ### `insertExtractMax` and `replaceMax` -/

#guard ((BinaryHeap.empty : BinaryHeap Nat).insertExtractMax 5).1 == 5
#guard ((#[3, 1, 4].toBinaryHeap).insertExtractMax 9).1 == 9
#guard ((#[3, 1, 4].toBinaryHeap).insertExtractMax 9).2.toSortedArray == #[4, 3, 1]
#guard ((#[3, 1, 4].toBinaryHeap).insertExtractMax 2).1 == 4
#guard ((#[3, 1, 4].toBinaryHeap).insertExtractMax 2).2.toSortedArray == #[3, 2, 1]

#guard ((BinaryHeap.empty : BinaryHeap Nat).replaceMax 5).1 == none
#guard ((BinaryHeap.empty : BinaryHeap Nat).replaceMax 5).2.toSortedArray == #[5]
#guard ((#[3, 1, 4].toBinaryHeap).replaceMax 9).1 == some 4
#guard ((#[3, 1, 4].toBinaryHeap).replaceMax 9).2.toSortedArray == #[9, 3, 1]
#guard ((#[3, 1, 4].toBinaryHeap).replaceMax 0).2.toSortedArray == #[3, 1, 0]

/-! ### `decreaseKey` and `increaseKey` -/

/-- Replace the element at index `i` using `decreaseKey`, or do nothing if out of range. -/
def decreaseAt (h : BinaryHeap Nat) (i : Nat) (x : Nat) : BinaryHeap Nat :=
  if hi : i < h.size then h.decreaseKey ⟨i, hi⟩ x else h

/-- Replace the element at index `i` using `increaseKey`, or do nothing if out of range. -/
def increaseAt (h : BinaryHeap Nat) (i : Nat) (x : Nat) : BinaryHeap Nat :=
  if hi : i < h.size then h.increaseKey ⟨i, hi⟩ x else h

#guard (decreaseAt (#[3, 1, 4, 1, 5].toBinaryHeap) 0 0).toSortedArray == #[4, 3, 1, 1, 0]
#guard (decreaseAt (#[3, 1, 4, 1, 5].toBinaryHeap) 0 0).max == some 4
#guard (increaseAt (#[3, 1, 4, 1, 5].toBinaryHeap) 4 9).max == some 9
#guard (increaseAt (#[3, 1, 4, 1, 5].toBinaryHeap) 4 9).size == 5

/-! ### Min-heap via `Ord.opposite` -/

section
local instance : Ord Nat := (inferInstance : Ord Nat).opposite

#guard (#[3, 1, 4, 1, 5].toBinaryHeap).max == some 1
#guard (#[3, 1, 4, 1, 5].toBinaryHeap).toSortedArray == #[1, 1, 3, 4, 5]
end

/-! ### Public lemmas are reachable with dot notation -/

example (a : Array Nat) : a.heapSort.Perm a := a.heapSort_perm
example (a : Array Nat) : a.heapSort.size = a.size := by simp
example (a : Array Nat) : a.heapSort.toList.Pairwise (compare · · |>.isLE) := a.heapSort_sorted
example (a : Array Nat) : a.toBinaryHeap.WF := Array.toBinaryHeap_wf
example (v : Vector Nat n) : v.toBinaryHeap.WF := Vector.toBinaryHeap_wf
example (h : BinaryHeap Nat) : h.toSortedArray.Perm h.arr := h.toSortedArray_perm
example (h : BinaryHeap Nat) (hwf : h.WF) (x : Nat) : (h.insert x).WF := BinaryHeap.insert_wf hwf
example (h : BinaryHeap Nat) (hwf : h.WF) : h.popMax.WF := BinaryHeap.popMax_wf hwf

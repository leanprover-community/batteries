/-
Copyright (c) 2021 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Batteries.Tactic.Lint.Misc
import Batteries.Tactic.SeqFocus

namespace Batteries

/-- Union-find node type -/
structure UFNode where
  /-- Parent of node -/
  parent : Nat
  /-- Rank of node -/
  rank : Nat

namespace UnionFind

/-- Panic with return value -/
def panicWith (v : α) (msg : String) : α := @panic α ⟨v⟩ msg

@[simp] theorem panicWith_eq (v : α) (msg) : panicWith v msg = v := rfl

/-- Parent of a union-find node, defaults to self when the node is a root -/
def parentD (arr : Array UFNode) (i : Nat) : Nat :=
  if h : i < arr.size then (arr.get ⟨i, h⟩).parent else i

/-- Rank of a union-find node, defaults to 0 when the node is a root -/
def rankD (arr : Array UFNode) (i : Nat) : Nat :=
  if h : i < arr.size then (arr.get ⟨i, h⟩).rank else 0

theorem parentD_eq {arr : Array UFNode} {i} : parentD arr i.1 = (arr.get i).parent := dif_pos _

theorem parentD_eq' {arr : Array UFNode} {i} (h) :
    parentD arr i = (arr.get ⟨i, h⟩).parent := dif_pos _

theorem rankD_eq {arr : Array UFNode} {i} : rankD arr i.1 = (arr.get i).rank := dif_pos _

theorem rankD_eq' {arr : Array UFNode} {i} (h) : rankD arr i = (arr.get ⟨i, h⟩).rank := dif_pos _

theorem parentD_of_not_lt : ¬i < arr.size → parentD arr i = i := (dif_neg ·)

theorem lt_of_parentD : parentD arr i ≠ i → i < arr.size :=
  Decidable.not_imp_comm.1 parentD_of_not_lt

theorem parentD_set {arr : Array UFNode} {x v i} :
    parentD (arr.set x v) i = if x.1 = i then v.parent else parentD arr i := by
  rw [parentD]; simp only [Array.size_set, Array.get_eq_getElem, parentD]
  split
  · split <;> simp_all
  · split <;> [(subst i; cases ‹¬_› x.2); rfl]

theorem rankD_set {arr : Array UFNode} {x v i} :
    rankD (arr.set x v) i = if x.1 = i then v.rank else rankD arr i := by
  rw [rankD]; simp only [Array.size_set, Array.get_eq_getElem, rankD]
  split
  · split <;> simp_all
  · split <;> [(subst i; cases ‹¬_› x.2); rfl]

end UnionFind

open UnionFind

/-- ### Union-find data structure

The `UnionFind` structure is an implementation of disjoint-set data structure
that uses path compression to make the primary operations run in amortized
nearly linear time. The nodes of a `UnionFind` structure `s` are natural
numbers smaller than `s.size`. The structure associates with a canonical
representative from its equivalence class. The structure can be extended
using the `push` operation and equivalence classes can be updated using the
`union` operation.

The main operations for `UnionFind` are:

* `empty`/`mkEmpty` are used to create a new empty structure.
* `size` returns the size of the data structure.
* `push` adds a new node to a structure, unlinked to any other node.
* `union` links two nodes of the data structure, joining their equivalence
  classes, and performs path compression.
* `find` returns the canonical representative of a node and updates the data
  structure using path compression.
* `root` returns the canonical representative of a node without altering the
  data structure.
* `checkEquiv` checks whether two nodes have the same canonical representative
  and updates the structure using path compression.

Most use cases should prefer `find` over `root` to benefit from the speedup from path-compression.

The main operations use `Fin s.size` to represent nodes of the union-find structure.
Some alternatives are provided:

* `unionN`, `findN`, `rootN`, `checkEquivN` use `Fin n` with a proof that `n = s.size`.
* `union!`, `find!`, `root!`, `checkEquiv!` use `Nat` and panic when the indices are out of bounds.
* `findD`, `rootD`, `checkEquivD` use `Nat` and treat out of bound indices as isolated nodes.

The noncomputable relation `UnionFind.Equiv` is provided to use the equivalence relation from a
`UnionFind` structure in the context of proofs.
-/
structure UnionFind where
  /-- Array of union-find nodes -/
  arr : Array UFNode
  /-- Validity for parent nodes -/
  parentD_lt : ∀ {i}, i < arr.size → parentD arr i < arr.size
  /-- Validity for rank -/
  rankD_lt : ∀ {i}, parentD arr i ≠ i → rankD arr i < rankD arr (parentD arr i)

namespace UnionFind

/-- Size of union-find structure. -/
@[inline] abbrev size (self : UnionFind) := self.arr.size

/-- Create an empty union-find structure with specific capacity -/
def mkEmpty (c : Nat) : UnionFind where
  arr := Array.mkEmpty c
  parentD_lt := nofun
  rankD_lt := nofun

/-- Empty union-find structure -/
def empty := mkEmpty 0

instance : EmptyCollection UnionFind := ⟨.empty⟩

/-- Parent of union-find node -/
abbrev parent (self : UnionFind) (i : Nat) : Nat := parentD self.arr i

theorem parent'_lt (self : UnionFind) (i : Fin self.size) :
    (self.arr.get i).parent < self.size := by
  simp only [← parentD_eq, parentD_lt, Fin.is_lt, Array.data_length]

theorem parent_lt (self : UnionFind) (i : Nat) : self.parent i < self.size ↔ i < self.size := by
  simp only [parentD]; split <;> simp only [*, parent'_lt]

/-- Rank of union-find node -/
abbrev rank (self : UnionFind) (i : Nat) : Nat := rankD self.arr i

theorem rank_lt {self : UnionFind} {i : Nat} : self.parent i ≠ i →
    self.rank i < self.rank (self.parent i) := by simpa only [rank] using self.rankD_lt

theorem rank'_lt (self : UnionFind) (i : Fin self.size) : (self.arr.get i).parent ≠ i →
    self.rank i < self.rank (self.arr.get i).parent := by
  simpa only [← parentD_eq] using self.rankD_lt

/-- Maximum rank of nodes in a union-find structure -/
noncomputable def rankMax (self : UnionFind) := self.arr.foldr (max ·.rank) 0 + 1

theorem rank'_lt_rankMax (self : UnionFind) (i : Fin self.size) :
    (self.arr.get i).rank < self.rankMax := by
  let rec go : ∀ {l} {x : UFNode}, x ∈ l → x.rank ≤ List.foldr (max ·.rank) 0 l
    | a::l, _, List.Mem.head _ => by dsimp; apply Nat.le_max_left
    | a::l, _, .tail _ h => by dsimp; exact Nat.le_trans (go h) (Nat.le_max_right ..)
  simp only [Array.get_eq_getElem, rankMax, Array.foldr_eq_foldr_data]
  exact Nat.lt_succ.2 <| go (self.arr.data.get_mem i.1 i.2)

theorem rankD_lt_rankMax (self : UnionFind) (i : Nat) :
    rankD self.arr i < self.rankMax := by
  simp [rankD]; split <;> [apply rank'_lt_rankMax; apply Nat.succ_pos]

theorem lt_rankMax (self : UnionFind) (i : Nat) : self.rank i < self.rankMax := rankD_lt_rankMax ..

theorem push_rankD (arr : Array UFNode) : rankD (arr.push ⟨arr.size, 0⟩) i = rankD arr i := by
  simp only [rankD, Array.size_push, Array.get_eq_getElem, Array.get_push, dite_eq_ite]
  split <;> split <;> first | simp | cases ‹¬_› (Nat.lt_succ_of_lt ‹_›)

theorem push_parentD (arr : Array UFNode) : parentD (arr.push ⟨arr.size, 0⟩) i = parentD arr i := by
  simp only [parentD, Array.size_push, Array.get_eq_getElem, Array.get_push, dite_eq_ite]
  split <;> split <;> try simp
  · exact Nat.le_antisymm (Nat.ge_of_not_lt ‹_›) (Nat.le_of_lt_succ ‹_›)
  · cases ‹¬_› (Nat.lt_succ_of_lt ‹_›)

/-- Add a new node to a union-find structure, unlinked with any other nodes -/
def push (self : UnionFind) : UnionFind where
  arr := self.arr.push ⟨self.arr.size, 0⟩
  parentD_lt {i} := by
    simp only [Array.size_push, push_parentD]; simp only [parentD, Array.get_eq_getElem]
    split <;> [exact fun _ => Nat.lt_succ_of_lt (self.parent'_lt _); exact id]
  rankD_lt := by simp only [push_parentD, ne_eq, push_rankD]; exact self.rank_lt

/-- Root of a union-find node. -/
def root (self : UnionFind) (x : Fin self.size) : Fin self.size :=
  let y := (self.arr.get x).parent
  if h : y = x then
    x
  else
    have := Nat.sub_lt_sub_left (self.lt_rankMax x) (self.rank'_lt _ h)
    self.root ⟨y, self.parent'_lt x⟩
termination_by self.rankMax - self.rank x

@[inherit_doc root]
def rootN (self : UnionFind) (x : Fin n) (h : n = self.size) : Fin n :=
  match n, h with | _, rfl => self.root x

/-- Root of a union-find node. Panics if index is out of bounds. -/
def root! (self : UnionFind) (x : Nat) : Nat :=
  if h : x < self.size then self.root ⟨x, h⟩ else panicWith x "index out of bounds"

/-- Root of a union-find node. Returns input if index is out of bounds. -/
def rootD (self : UnionFind) (x : Nat) : Nat :=
  if h : x < self.size then self.root ⟨x, h⟩ else x

@[nolint unusedHavesSuffices]
theorem parent_root (self : UnionFind) (x : Fin self.size) :
    (self.arr.get (self.root x)).parent = self.root x := by
  rw [root]; split <;> [assumption; skip]
  have := Nat.sub_lt_sub_left (self.lt_rankMax x) (self.rank'_lt _ ‹_›)
  apply parent_root
termination_by self.rankMax - self.rank x

theorem parent_rootD (self : UnionFind) (x : Nat) :
    self.parent (self.rootD x) = self.rootD x := by
  rw [rootD]
  split
  · simp [parentD, parent_root, -Array.get_eq_getElem]
  · simp [parentD_of_not_lt, *]

@[nolint unusedHavesSuffices]
theorem rootD_parent (self : UnionFind) (x : Nat) : self.rootD (self.parent x) = self.rootD x := by
  simp only [rootD, Array.data_length, parent_lt]
  split
  · simp only [parentD, ↓reduceDIte, *]
    (conv => rhs; rw [root]); split
    · rw [root, dif_pos] <;> simp_all
    · simp
  · simp only [not_false_eq_true, parentD_of_not_lt, *]

theorem rootD_lt {self : UnionFind} {x : Nat} : self.rootD x < self.size ↔ x < self.size := by
  simp only [rootD, Array.data_length]; split <;> simp [*]

@[nolint unusedHavesSuffices]
theorem rootD_eq_self {self : UnionFind} {x : Nat} : self.rootD x = x ↔ self.parent x = x := by
  refine ⟨fun h => by rw [← h, parent_rootD], fun h => ?_⟩
  rw [rootD]; split <;> [rw [root, dif_pos (by rwa [parent, parentD_eq' ‹_›] at h)]; rfl]

theorem rootD_rootD {self : UnionFind} {x : Nat} : self.rootD (self.rootD x) = self.rootD x :=
  rootD_eq_self.2 (parent_rootD ..)

theorem rootD_ext {m1 m2 : UnionFind}
    (H : ∀ x, m1.parent x = m2.parent x) {x} : m1.rootD x = m2.rootD x := by
  if h : m2.parent x = x then
    rw [rootD_eq_self.2 h, rootD_eq_self.2 ((H _).trans h)]
  else
    have := Nat.sub_lt_sub_left (m2.lt_rankMax x) (m2.rank_lt h)
    rw [← rootD_parent, H, rootD_ext H, rootD_parent]
termination_by m2.rankMax - m2.rank x

theorem le_rank_root {self : UnionFind} {x : Nat} : self.rank x ≤ self.rank (self.rootD x) := by
  if h : self.parent x = x then
    rw [rootD_eq_self.2 h]; exact Nat.le_refl ..
  else
    have := Nat.sub_lt_sub_left (self.lt_rankMax x) (self.rank_lt h)
    rw [← rootD_parent]
    exact Nat.le_trans (Nat.le_of_lt (self.rank_lt h)) le_rank_root
termination_by self.rankMax - self.rank x

theorem lt_rank_root {self : UnionFind} {x : Nat} :
    self.rank x < self.rank (self.rootD x) ↔ self.parent x ≠ x := by
  refine ⟨fun h h' => Nat.ne_of_lt h (by rw [rootD_eq_self.2 h']), fun h => ?_⟩
  rw [← rootD_parent]
  exact Nat.lt_of_lt_of_le (self.rank_lt h) le_rank_root

/-- Auxiliary data structure for find operation -/
structure FindAux (n : Nat) where
  /-- Array of nodes -/
  s : Array UFNode
  /-- Index of root node -/
  root : Fin n
  /-- Size requirement -/
  size_eq : s.size = n

/-- Auxiliary function for find operation -/
def findAux (self : UnionFind) (x : Fin self.size) : FindAux self.size :=
  let y := (self.arr.get x).parent
  if h : y = x then
    ⟨self.arr, x, rfl⟩
  else
    have := Nat.sub_lt_sub_left (self.lt_rankMax x) (self.rank'_lt _ h)
    let ⟨arr₁, root, H⟩ := self.findAux ⟨y, self.parent'_lt x⟩
    ⟨arr₁.modify x fun s => { s with parent := root }, root, by simp [H]⟩
termination_by self.rankMax - self.rank x

@[nolint unusedHavesSuffices]
theorem findAux_root {self : UnionFind} {x : Fin self.size} :
    (findAux self x).root = self.root x := by
  rw [findAux, root]
  simp only [Array.data_length, Array.get_eq_getElem, dite_eq_ite]
  split <;> simp only
  have := Nat.sub_lt_sub_left (self.lt_rankMax x) (self.rank'_lt _ ‹_›)
  exact findAux_root
termination_by self.rankMax - self.rank x

@[nolint unusedHavesSuffices]
theorem findAux_s {self : UnionFind} {x : Fin self.size} :
    (findAux self x).s = if (self.arr.get x).parent = x then self.arr else
      (self.findAux ⟨_, self.parent'_lt x⟩).s.modify x fun s =>
        { s with parent := self.rootD x } := by
  rw [show self.rootD _ = (self.findAux ⟨_, self.parent'_lt x⟩).root from _]
  · rw [findAux]; split <;> rfl
  · rw [← rootD_parent, parent, parentD_eq]
    simp only [rootD, Array.get_eq_getElem, Array.data_length, findAux_root]
    apply dif_pos
    exact parent'_lt ..

theorem rankD_findAux {self : UnionFind} {x : Fin self.size} :
    rankD (findAux self x).s i = self.rank i := by
  if h : i < self.size then
    rw [findAux_s]; split <;> [rfl; skip]
    have := Nat.sub_lt_sub_left (self.lt_rankMax x) (self.rank'_lt _ ‹_›)
    have := lt_of_parentD (by rwa [parentD_eq])
    rw [rankD_eq' (by simp [FindAux.size_eq, h]), Array.get_modify (by rwa [FindAux.size_eq])]
    split <;> simp [← rankD_eq, rankD_findAux (x := ⟨_, self.parent'_lt x⟩), -Array.get_eq_getElem]
  else
    simp only [rankD, Array.data_length, Array.get_eq_getElem, rank]
    rw [dif_neg (by rwa [FindAux.size_eq]), dif_neg h]
termination_by self.rankMax - self.rank x

theorem parentD_findAux {self : UnionFind} {x : Fin self.size} :
    parentD (findAux self x).s i =
    if i = x then self.rootD x else parentD (self.findAux ⟨_, self.parent'_lt x⟩).s i := by
  rw [findAux_s]; split <;> [split; skip]
  · subst i; rw [rootD_eq_self.2 _] <;> simp [parentD_eq, *, -Array.get_eq_getElem]
  · rw [findAux_s]; simp [*, -Array.get_eq_getElem]
  · next h =>
    rw [parentD]; split <;> rename_i h'
    · rw [Array.get_modify (by simpa using h')]
      simp only [Array.data_length, @eq_comm _ i]
      split <;> simp [← parentD_eq, -Array.get_eq_getElem]
    · rw [if_neg (mt (by rintro rfl; simp [FindAux.size_eq]) h')]
      rw [parentD, dif_neg]; simpa using h'

theorem parentD_findAux_rootD {self : UnionFind} {x : Fin self.size} :
    parentD (findAux self x).s (self.rootD x) = self.rootD x := by
  rw [parentD_findAux]; split <;> [rfl; rename_i h]
  rw [rootD_eq_self, parent, parentD_eq] at h
  have := Nat.sub_lt_sub_left (self.lt_rankMax x) (self.rank'_lt _ ‹_›)
  rw [← rootD_parent, parent, parentD_eq]
  exact parentD_findAux_rootD (x := ⟨_, self.parent'_lt x⟩)
termination_by self.rankMax - self.rank x

theorem parentD_findAux_lt {self : UnionFind} {x : Fin self.size} (h : i < self.size) :
    parentD (findAux self x).s i < self.size := by
  if h' : (self.arr.get x).parent = x then
    rw [findAux_s, if_pos h']; apply self.parentD_lt h
  else
    rw [parentD_findAux]
    split
    · simp [rootD_lt]
    · have := Nat.sub_lt_sub_left (self.lt_rankMax x) (self.rank'_lt _ ‹_›)
      apply parentD_findAux_lt h
termination_by self.rankMax - self.rank x

theorem parentD_findAux_or (self : UnionFind) (x : Fin self.size) (i) :
    parentD (findAux self x).s i = self.rootD i ∧ self.rootD i = self.rootD x ∨
    parentD (findAux self x).s i = self.parent i := by
  if h' : (self.arr.get x).parent = x then
    rw [findAux_s, if_pos h']; exact .inr rfl
  else
    rw [parentD_findAux]
    split
    · simp [*]
    · have := Nat.sub_lt_sub_left (self.lt_rankMax x) (self.rank'_lt _ ‹_›)
      exact (parentD_findAux_or self ⟨_, self.parent'_lt x⟩ i).imp_left <| .imp_right fun h => by
        simp only [h, ← parentD_eq, rootD_parent, Array.data_length]
termination_by self.rankMax - self.rank x

theorem lt_rankD_findAux {self : UnionFind} {x : Fin self.size} :
    parentD (findAux self x).s i ≠ i →
    self.rank i < self.rank (parentD (findAux self x).s i) := by
  if h' : (self.arr.get x).parent = x then
    rw [findAux_s, if_pos h']; apply self.rank_lt
  else
    rw [parentD_findAux]; split <;> rename_i h <;> intro h'
    · subst i; rwa [lt_rank_root, Ne, ← rootD_eq_self]
    · have := Nat.sub_lt_sub_left (self.lt_rankMax x) (self.rank'_lt _ ‹_›)
      apply lt_rankD_findAux h'
termination_by self.rankMax - self.rank x

/-- Find root of a union-find node, updating the structure using path compression. -/
def find (self : UnionFind) (x : Fin self.size) :
    (s : UnionFind) × {_root : Fin s.size // s.size = self.size} :=
  let r := self.findAux x
  { 1.arr := r.s
    2.1.val := r.root
    1.parentD_lt := fun h => by
      simp only [Array.data_length, FindAux.size_eq] at *
      exact parentD_findAux_lt h
    1.rankD_lt := fun h => by rw [rankD_findAux, rankD_findAux]; exact lt_rankD_findAux h
    2.1.isLt := show _ < r.s.size by rw [r.size_eq]; exact r.root.2
    2.2 := by simp [size, r.size_eq] }

@[inherit_doc find]
def findN (self : UnionFind) (x : Fin n) (h : n = self.size) : UnionFind × Fin n :=
  match n, h with | _, rfl => match self.find x with | ⟨s, r, h⟩ => (s, Fin.cast h r)

/-- Find root of a union-find node, updating the structure using path compression.
  Panics if index is out of bounds. -/
def find! (self : UnionFind) (x : Nat) : UnionFind × Nat :=
  if h : x < self.size then
    match self.find ⟨x, h⟩ with | ⟨s, r, _⟩ => (s, r)
  else
    panicWith (self, x) "index out of bounds"

/-- Find root of a union-find node, updating the structure using path compression.
  Returns inputs unchanged when index is out of bounds. -/
def findD (self : UnionFind) (x : Nat) : UnionFind × Nat :=
  if h : x < self.size then
    match self.find ⟨x, h⟩ with | ⟨s, r, _⟩ => (s, r)
  else
    (self, x)

@[simp] theorem find_size (self : UnionFind) (x : Fin self.size) :
    (self.find x).1.size = self.size := by simp [find, size, FindAux.size_eq]

@[simp] theorem find_root_2 (self : UnionFind) (x : Fin self.size) :
    (self.find x).2.1.1 = self.rootD x := by simp [find, findAux_root, rootD]

@[simp] theorem find_parent_1 (self : UnionFind) (x : Fin self.size) :
    (self.find x).1.parent x = self.rootD x := by
  simp only [parent, Array.data_length, find]
  rw [parentD_findAux, if_pos rfl]

theorem find_parent_or (self : UnionFind) (x : Fin self.size) (i) :
    (self.find x).1.parent i = self.rootD i ∧ self.rootD i = self.rootD x ∨
    (self.find x).1.parent i = self.parent i := parentD_findAux_or ..

@[simp] theorem find_root_1 (self : UnionFind) (x : Fin self.size) (i : Nat) :
    (self.find x).1.rootD i = self.rootD i := by
  if h : (self.find x).1.parent i = i then
    rw [rootD_eq_self.2 h]
    obtain ⟨h1, _⟩ | h1 := find_parent_or self x i <;> rw [h1] at h
    · rw [h]
    · rw [rootD_eq_self.2 h]
  else
    have := Nat.sub_lt_sub_left ((self.find x).1.lt_rankMax _) ((self.find x).1.rank_lt h)
    rw [← rootD_parent, find_root_1 self x ((self.find x).1.parent i)]
    obtain ⟨h1, _⟩ | h1 := find_parent_or self x i
    · rw [h1, rootD_rootD]
    · rw [h1, rootD_parent]
termination_by  (self.find x).1.rankMax - (self.find x).1.rank i
decreasing_by exact this -- why is this needed? It is way slower without it

/-- Link two union-find nodes -/
def linkAux (self : Array UFNode) (x y : Fin self.size) : Array UFNode :=
  if x.1 = y then
    self
  else
    let nx := self.get x
    let ny := self.get y
    if ny.rank < nx.rank then
      self.set y {ny with parent := x}
    else
      let arr₁ := self.set x {nx with parent := y}
      if nx.rank = ny.rank then
        arr₁.set ⟨y, by simp [arr₁]⟩ {ny with rank := ny.rank + 1}
      else
        arr₁

theorem setParentBump_rankD_lt {arr : Array UFNode} {x y : Fin arr.size}
    (hroot : (arr.get x).rank < (arr.get y).rank ∨ (arr.get y).parent = y)
    (H : (arr.get x).rank ≤ (arr.get y).rank) {i : Nat}
    (rankD_lt : parentD arr i ≠ i → rankD arr i < rankD arr (parentD arr i))
    (hP : parentD arr' i = if x.1 = i then y.1 else parentD arr i)
    (hR : ∀ {i}, rankD arr' i =
      if y.1 = i ∧ (arr.get x).rank = (arr.get y).rank then
        (arr.get y).rank + 1
      else rankD arr i) :
    ¬parentD arr' i = i → rankD arr' i < rankD arr' (parentD arr' i) := by
  simp [hP, hR, -Array.get_eq_getElem] at *; split <;> rename_i h₁ <;> [simp [← h₁]; skip] <;>
    split <;> rename_i h₂ <;> intro h
  · simp [h₂] at h
  · simp only [rankD_eq, Array.get_eq_getElem]
    split <;> rename_i h₃
    · rw [← h₃]; apply Nat.lt_succ_self
    · exact Nat.lt_of_le_of_ne H h₃
  · cases h₂.1
    simp only [h₂.2, false_or, Nat.lt_irrefl] at hroot
    simp only [hroot, parentD_eq, not_true_eq_false] at h
  · have := rankD_lt h
    split <;> rename_i h₃
    · rw [← rankD_eq, h₃.1]; exact Nat.lt_succ_of_lt this
    · exact this

theorem setParent_rankD_lt {arr : Array UFNode} {x y : Fin arr.size}
    (h : (arr.get x).rank < (arr.get y).rank) {i : Nat}
    (rankD_lt : parentD arr i ≠ i → rankD arr i < rankD arr (parentD arr i)) :
    let arr' := arr.set x ⟨y, (arr.get x).rank⟩
    parentD arr' i ≠ i → rankD arr' i < rankD arr' (parentD arr' i) :=
  setParentBump_rankD_lt (.inl h) (Nat.le_of_lt h) rankD_lt parentD_set
    (by simp [rankD_set, Nat.ne_of_lt h, rankD_eq, -Array.get_eq_getElem])

@[simp] theorem linkAux_size : (linkAux self x y).size = self.size := by
  simp only [linkAux, Array.get_eq_getElem]
  split <;> [rfl; split] <;> [skip; split] <;> simp

/-- Link a union-find node to a root node. -/
def link (self : UnionFind) (x y : Fin self.size) (yroot : self.parent y = y) : UnionFind where
  arr := linkAux self.arr x y
  parentD_lt h := by
    simp only [Array.data_length, linkAux_size] at *
    simp only [linkAux, Array.get_eq_getElem]
    split <;> [skip; split <;> [skip; split]]
    · exact self.parentD_lt h
    · rw [parentD_set]; split <;> [exact x.2; exact self.parentD_lt h]
    · rw [parentD_set]; split
      · exact self.parent'_lt _
      · rw [parentD_set]; split <;> [exact y.2; exact self.parentD_lt h]
    · rw [parentD_set]; split <;> [exact y.2; exact self.parentD_lt h]
  rankD_lt := by
    rw [parent, parentD_eq] at yroot
    simp only [linkAux, Array.get_eq_getElem, ne_eq]
    split <;> [skip; split <;> [skip; split]]
    · exact self.rankD_lt
    · exact setParent_rankD_lt ‹_› self.rankD_lt
    · refine setParentBump_rankD_lt (.inr yroot) (Nat.le_of_eq ‹_›) self.rankD_lt (by
        simp only [parentD_set, ite_eq_right_iff]
        rintro rfl
        simp [*, parentD_eq]) fun {i} => ?_
      simp only [rankD_set, Fin.eta, Array.get_eq_getElem]
      split
      · simp_all
      · simp_all only [Array.get_eq_getElem, Array.data_length, Nat.lt_irrefl, not_false_eq_true,
          and_true, ite_false, ite_eq_right_iff]
        rintro rfl
        simp [rankD_eq, *]
    · exact setParent_rankD_lt (Nat.lt_of_le_of_ne (Nat.not_lt.1 ‹_›) ‹_›) self.rankD_lt

@[inherit_doc link]
def linkN (self : UnionFind) (x y : Fin n) (yroot : self.parent y = y) (h : n = self.size) :
    UnionFind := match n, h with | _, rfl => self.link x y yroot

/-- Link a union-find node to a root node. Panics if either index is out of bounds. -/
def link! (self : UnionFind) (x y : Nat) (yroot : self.parent y = y) : UnionFind :=
  if h : x < self.size ∧ y < self.size then
    self.link ⟨x, h.1⟩ ⟨y, h.2⟩ yroot
  else
    panicWith self "index out of bounds"

/-- Link two union-find nodes, uniting their respective classes. -/
def union (self : UnionFind) (x y : Fin self.size) : UnionFind :=
  let ⟨self₁, rx, ex⟩ := self.find x
  have hy := by rw [ex]; exact y.2
  match eq : self₁.find ⟨y, hy⟩ with
  | ⟨self₂, ry, ey⟩ =>
    self₂.link ⟨rx, by rw [ey]; exact rx.2⟩ ry <| by
      have := find_root_1 self₁ ⟨y, hy⟩ (⟨y, hy⟩ : Fin _)
      rw [← find_root_2, eq] at this; simp at this
      rw [← this, parent_rootD]

@[inherit_doc union]
def unionN (self : UnionFind) (x y : Fin n) (h : n = self.size) : UnionFind :=
  match n, h with | _, rfl => self.union x y

/-- Link two union-find nodes, uniting their respective classes.
Panics if either index is out of bounds. -/
def union! (self : UnionFind) (x y : Nat) : UnionFind :=
  if h : x < self.size ∧ y < self.size then
    self.union ⟨x, h.1⟩ ⟨y, h.2⟩
  else
    panicWith self "index out of bounds"

/-- Check whether two union-find nodes are equivalent, updating structure using path compression. -/
def checkEquiv (self : UnionFind) (x y : Fin self.size) : UnionFind × Bool :=
  let ⟨s, ⟨r₁, _⟩, h⟩ := self.find x
  let ⟨s, ⟨r₂, _⟩, _⟩ := s.find (h ▸ y)
  (s, r₁ == r₂)

@[inherit_doc checkEquiv]
def checkEquivN (self : UnionFind) (x y : Fin n) (h : n = self.size) : UnionFind × Bool :=
  match n, h with | _, rfl => self.checkEquiv x y

/-- Check whether two union-find nodes are equivalent, updating structure using path compression.
Panics if either index is out of bounds. -/
def checkEquiv! (self : UnionFind) (x y : Nat) : UnionFind × Bool :=
  if h : x < self.size ∧ y < self.size then
    self.checkEquiv ⟨x, h.1⟩ ⟨y, h.2⟩
  else
    panicWith (self, false) "index out of bounds"

/-- Check whether two union-find nodes are equivalent with path compression,
returns `x == y` if either index is out of bounds -/
def checkEquivD (self : UnionFind) (x y : Nat) : UnionFind × Bool :=
  let (s, x) := self.findD x
  let (s, y) := s.findD y
  (s, x == y)

/-- Equivalence relation from a `UnionFind` structure -/
def Equiv (self : UnionFind) (a b : Nat) : Prop := self.rootD a = self.rootD b

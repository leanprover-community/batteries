/-
Copyright (c) 2026 Chad Sharp. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chad Sharp
-/
module
public import Batteries.Data.BinaryHeap.Basic
public import Batteries.Data.BinaryHeap.WF
import all Batteries.Data.BinaryHeap.WF
import all Batteries.Data.BinaryHeap.Basic

namespace Batteries.BinaryHeap

/-- If maxChild returns none, there are no children in bounds. -/
theorem maxChild_none_iff [Ord α] {a : Vector α sz} {i : Fin sz} :
    maxChild a i = none ↔ sz ≤ 2 * i.val + 1 := by
  grind only [maxChild]

/-- maxChild returns some iff there is at least one child. -/
theorem maxChild_some_iff [Ord α] {a : Vector α sz} {i : Fin sz} :
    (maxChild a i).isSome ↔ 2 * i.val + 1 < sz := by
  grind only [maxChild, = Option.isSome]

/-- If maxChild returns some j, then j is a child of i. -/
theorem maxChild_isChild [Ord α] {a : Vector α sz} {i : Fin sz} {j : Fin sz}
    (h : maxChild a i = some j) :
    j.val = 2 * i.val + 1 ∨ j.val = 2 * i.val + 2 := by
  grind only [maxChild, = Option.isSome]

/-- maxChild returns an index greater than i. -/
theorem maxChild_gt [Ord α] {a : Vector α sz} {i : Fin sz} {j : Fin sz}
    (h : maxChild a i = some j) : i < j := by
  grind only [maxChild, Lean.Grind.toInt_fin]

theorem maxChild_ge_left [Ord α] [Std.OrientedOrd α] (a : Vector α sz) (i j : Fin sz)
    (hmc : maxChild a i = some j) (hleft : 2 * i.val + 1 < sz) :
    compare a[j] a[2 * i.val + 1] |>.isGE := by
  grind only [Std.OrientedOrd.eq_swap, Ordering.swap_lt, Ordering.isGE, Ordering.isLT, maxChild,
  Fin.getElem_fin]

theorem maxChild_ge_right [Ord α] [Std.OrientedOrd α] (a : Vector α sz)
    (i j : Fin sz) (hmc : maxChild a i = some j) (hright : 2 * i.val + 2 < sz) :
    compare a[↑j] a[2 * ↑i + 2] |>.isGE := by
  grind only [= Fin.getElem_fin, Std.OrientedOrd.eq_swap, Ordering.swap_lt,
    Ordering.isGE, Ordering.isLT, maxChild]

section heapifyDown

/-- heapifyDown doesn't modify positions before the starting index. -/
theorem heapifyDown_preserves_prefix [Ord α] (a : Vector α sz) (i k : Fin sz) (hk : k < ↑i) :
    (heapifyDown a i)[k] = a[k] := by
  induction a, i using heapifyDown.induct
    <;> grind only [heapifyDown, = Fin.getElem_fin, = Vector.getElem_swap]

/-- When maxChild returns none, heapifyDown is the identity. -/
@[simp]
theorem heapifyDown_eq_of_maxChild_none [Ord α] {a : Vector α sz} {i : Fin sz}
    (h : maxChild a i = none) :
    heapifyDown a i = a := by
  grind only [heapifyDown]

/-- When maxChild returns some and the parent is less than the child,
  heapifyDown swaps and recurses. -/
theorem heapifyDown_eq_of_lt [Ord α] {a : Vector α sz} {i j : Fin sz}
    (hmaxChild : maxChild a i = some j) (h_lt : (compare a[i] a[j]).isLT) :
    heapifyDown a i = heapifyDown (a.swap i j) j := by
  grind only [heapifyDown]

/-- When maxChild returns some but parent is not less than child, heapifyDown is the identity. -/
theorem heapifyDown_eq_of_not_lt [Ord α] {a : Vector α sz} {i j : Fin sz}
    (hmaxChild : maxChild a i = some j) (h_not_lt : ¬(compare a[i] a[j]).isLT) :
    heapifyDown a i = a := by
  grind only [heapifyDown]

/-- `heapifyDown` does not modify elements outside the subtree rooted at `i`. -/
theorem heapifyDown_get_of_not_inSubtree [Ord α] {a : Vector α sz} {i : Fin sz}
    {k : Fin sz} (hnsub : ¬InSubtree i k) :
    (heapifyDown a i)[k] = a[k] := by
  cases hmc : maxChild a i with
  | none => simp_all
  | some j =>
    have hij : i < j := maxChild_gt hmc
    by_cases h_lt : (compare a[i] a[j]).isLT
    · rw [heapifyDown_eq_of_lt ‹_› ‹_›]
      have hnsub_j : ¬InSubtree j k := by
        intro hsub_jk
        exact hnsub (InSubtree.of_child (maxChild_isChild hmc) |>.trans hsub_jk)
      rw [heapifyDown_get_of_not_inSubtree hnsub_j]
      grind only [= Fin.getElem_fin, Vector.getElem_swap_of_ne, InSubtree]
    · simp_all [heapifyDown_eq_of_not_lt]
termination_by sz - i

/-- `heapifyDown` preserves `WF.children` for nodes completely outside the affected subtree. -/
theorem heapifyDown_get_of_not_inSubtree' [Ord α] {a : Vector α sz} {i : Fin sz}
    {k : Nat} (hk : k < sz) (hnsub : ¬InSubtree i k) :
    (heapifyDown a i)[k] = a[k] :=
  heapifyDown_get_of_not_inSubtree (k := ⟨k, hk⟩) hnsub

/-- `heapifyDown` preserves `WF.children` for nodes completely outside the affected subtree. -/
theorem heapifyDown_preserves_wf_children_of_not_inSubtree [Ord α]
    {a b : Vector α sz} {i k : Fin sz}
    (hnsub_k : ¬InSubtree i k) (hk_eq : a[k] = b[k])
    (hleft_eq : ∀ h : 2 * k.val + 1 < sz, a[2 * k.val + 1] = b[2 * k.val + 1])
    (hright_eq : ∀ h : 2 * k.val + 2 < sz, a[2 * k.val + 2] = b[2 * k.val + 2])
    (hwf : WF.children b k)
    (hnsub_left : i ≠ 2 * k.val + 1)
    (hnsub_right : i ≠ 2 * k.val + 2) :
    WF.children (heapifyDown a i) k := by
  obtain ⟨hwf_left, hwf_right⟩ := hwf
  constructor
  all_goals
    intro hbound
    rw [heapifyDown_get_of_not_inSubtree hnsub_k,
        heapifyDown_get_of_not_inSubtree' hbound (by grind only)]
    simp_all

/-- heapifyDown at j preserves WF.children k when i < k < j and j is a child of i -/
theorem heapifyDown_swap_preserves_wf_children_of_lt [Ord α] {a : Vector α sz} {i j k : Fin sz}
    (hchild : j.val = 2 * i.val + 1 ∨ j.val = 2 * i.val + 2)
    (hik : i < k) (hkj : k < j) (hwf : WF.children a k) :
    WF.children (heapifyDown (a.swap ↑i ↑j) ↑j) ↑k :=
  heapifyDown_preserves_wf_children_of_not_inSubtree
    (InSubtree.not_of_lt (by omega))
    (Vector.getElem_swap_of_ne (by omega) (by omega))
    (fun _ => Vector.getElem_swap_of_ne (by omega) (by omega))
    (fun _ => Vector.getElem_swap_of_ne (by omega) (by omega))
    hwf
    (by omega)
    (by omega)

theorem heapifyDown_preserves_wf_children_outside [Ord α] {v : Vector α sz} {i k : Fin sz}
    (hki : k < i) (hwf : WF.children v k)
    (hleft_ne : i.val ≠ 2 * k.val + 1 ) (hright_ne : i.val ≠ 2 * k.val + 2) :
    WF.children (heapifyDown v i) k :=
  heapifyDown_preserves_wf_children_of_not_inSubtree
    (InSubtree.not_of_lt hki) rfl (fun _ => rfl) (fun _ => rfl) hwf hleft_ne hright_ne

/-- If v dominates all values in the subtree, v dominates the result at root -/
theorem heapifyDown_root_bounded [Ord α] [Std.TransOrd α]
    {a : Vector α sz} {j : Fin sz} {v : α}
    (hge : ∀ k : Fin sz, InSubtree j.val k.val → (compare v a[k]).isGE) :
    (compare v (heapifyDown a j)[j]).isGE := by
  grind only [heapifyDown, InSubtree, Fin.getElem_fin, maxChild_isChild,
    = heapifyDown_preserves_prefix, = Vector.getElem_swap]

/-- heapifyDown at i preserves WF.children at parent of i when value decreased -/
theorem heapifyDown_preserves_wf_parent [Ord α] [Std.TransOrd α] [Std.OrientedOrd α]
    {v : Vector α sz} {i : Fin sz} {x : α}
    (htd : WF.topDown v) (h_le : compare x v[i] |>.isLE) (hi : 0 < i.val) :
    WF.children (heapifyDown (v.set i x) i) ⟨(i.val - 1) / 2, by omega⟩ := by
  let parent : Fin sz := ⟨(i.val - 1) / 2, by omega⟩
  have h_parent_lt_i : parent < i := by grind only [Lean.Grind.toInt_fin]
  have hk_not_sub : ¬InSubtree i parent := InSubtree.not_of_lt h_parent_lt_i
  obtain ⟨hwf_parent_l, hwf_parent_r⟩ := htd parent
  have h_parent_child : i.val = 2 * parent.val + 1 ∨ i.val = 2 * parent.val + 2 := by grind only
  constructor
  case' left  => let childIdx := 2 * parent.val + 1
  case' right => let childIdx := 2 * parent.val + 2
  all_goals
    intro hside
    rw [heapifyDown_get_of_not_inSubtree hk_not_sub]
    have : parent.val ≠ i.val := by omega
    simp only [Fin.getElem_fin]
    rw [Vector.getElem_set_ne (i := i.val) (j := parent.val) _ _ (by omega)]
    by_cases heq : childIdx = i.val
    · simp only [parent, heq, childIdx]
      apply heapifyDown_root_bounded
      apply WF.parent_dominates_set_subtree <;> assumption
    . have hsub : ¬InSubtree i.val childIdx :=  by grind only [InSubtree.not_of_lt]
      rw [heapifyDown_get_of_not_inSubtree' hside hsub]
      rw [Vector.getElem_set_ne _ _ (by simp_all only [ne_eq]; omega)]
      simp_all [childIdx, parent]

theorem heapifyDown_perm [Ord α] {a : Vector α sz} {i : Fin sz} :
    (heapifyDown a i).Perm a := by
  induction a, i using heapifyDown.induct with
    | case1 => simp_all [heapifyDown_eq_of_maxChild_none]
    | case2 a i j hmaxChild hij hlt ih =>
      rw [heapifyDown_eq_of_lt ‹_› ‹_›]
      apply ih.trans
      simp_all [Vector.swap_perm]
    | case3 =>
      simp_all [heapifyDown_eq_of_not_lt]

/-- a[j] dominates everything in (a.swap i j)'s subtree at j when i < j and a[i] < a[j] -/
theorem swap_child_dominates [Ord α] [Std.TransOrd α] [Std.OrientedOrd α]
    {a : Vector α sz} {i j : Fin sz} (h_ij : i < j) (h_lt : (compare a[i] a[j]).isLT)
    (hbelow : WF.below a i) (k : Fin sz) (hsub : InSubtree j k) :
    (compare a[j] (a.swap i j i.isLt j.isLt)[k]).isGE := by
  by_cases hk_eq_j : k.val = j.val
  · unfold Ordering.isGE
    rw [Std.OrientedOrd.eq_swap]
    simp_all
  · have hi' : k.val ≠ i.val := InSubtree.ne_of_lt h_ij hsub
    simp_all [WF.parent_ge_subtree, hbelow j h_ij, Vector.getElem_swap_of_ne,
      WF.below_of_le (Fin.le_of_lt h_ij) hbelow]

/-- After swapping with maxChild and heapifying, WF.children holds at the original position i.

We show a[j] (now at position i after swap) dominates both children of i.
Four cases arise from: (proving left vs right child) × (j is left vs right child).
- left.inl, right.inr: j equals the child we're proving about → use heapifyDown_root_bounded
- left.inr, right.inl: j is the sibling → sibling unchanged, use maxChild_ge_left/right -/
theorem heapifyDown_swap_wf_children [Ord α] [Std.TransOrd α] [Std.OrientedOrd α]
    {a : Vector α sz} {i j : Fin sz}
    (hmaxChild : maxChild a i = some j)
    (h_lt : (compare a[i] a[j]).isLT)
    (hbelow : WF.below a i) :
    WF.children (heapifyDown (a.swap i j) j) i := by
  have h_ij : i < j := maxChild_gt hmaxChild
  have hnsub_i : ¬InSubtree j.val i.val := InSubtree.not_of_lt h_ij
  have hchild := maxChild_isChild hmaxChild
  constructor
  all_goals
    intro hside
    -- Position i now contains a[j] (via swap), unchanged by heapifyDown (i outside j's subtree)
    simp only [heapifyDown_get_of_not_inSubtree hnsub_i, Fin.getElem_fin,
      Vector.getElem_swap_left]
    cases hchild
  -- j equals the child we're proving about: a[j] dominates the heapified result at j
  case left.inl | right.inr =>
    have : (compare a[j] (heapifyDown (a.swap i j) j)[j]).isGE = true := by
      apply heapifyDown_root_bounded
      apply swap_child_dominates <;> assumption
    simp_all
  -- j is the sibling: sibling is outside j's subtree, unchanged; maxChild guarantees a[j] >= sibling
  case' left.inr  => let childIdx := 2 * i.val + 1
  case' right.inl => let childIdx := 2 * i.val + 2
  all_goals
    have hnsub : ¬InSubtree j.val childIdx := by grind only [InSubtree.not_of_lt]
    rw [heapifyDown_get_of_not_inSubtree' hside hnsub]
    rw [Vector.getElem_swap_of_ne (by omega) (by omega)]
    first | apply maxChild_ge_left | apply maxChild_ge_right
    assumption

/-- If parent >= maxChild, then WF.children holds at that position. -/
theorem wf_children_of_ge_maxChild [Ord α] [Std.TransOrd α] [Std.OrientedOrd α]
    {a : Vector α sz} {i j : Fin sz}
    (hmaxChild : maxChild a i = some j)
    (h_ge : (compare a[i] a[j]).isGE) :
    WF.children a i := by
  constructor
    <;> intros
    <;> apply Std.TransOrd.isGE_trans h_ge
    <;> (first | apply maxChild_ge_left | apply maxChild_ge_right)
    <;> assumption

/-- `heapifyDown` restores the heap property at node `i` and below, given that all nodes
below `i` already satisfy `WF.children`. -/
theorem heapifyDown_wf [Ord α] [Std.TransOrd α] [Std.OrientedOrd α]
    {a : Vector α sz} {i : Fin sz}
    (hbelow : WF.below a i) :
    WF.children (heapifyDown a i) i ∧ WF.below (heapifyDown a i) i := by
  induction a, i using heapifyDown.induct with
  | case1 a i h => grind only [WF.children, WF.below, maxChild]
  | case2 a i j hmaxChild h_ij h_ai_aj ih =>
    rw [heapifyDown_eq_of_lt ‹_› ‹_›]
    obtain ⟨ih_at, ih_below⟩ := ih (WF.below_swap (hbelow := hbelow) (hij := h_ij))
    have hchild := maxChild_isChild hmaxChild
    constructor
    · apply heapifyDown_swap_wf_children <;> assumption
    · intro k hik
      cases Nat.lt_trichotomy j k <;> grind only [heapifyDown_swap_preserves_wf_children_of_lt,
        WF.children, WF.below, = Fin.getElem_fin]
  | case3 a i j hmaxChild hij h_nlt =>
      simp_all [wf_children_of_ge_maxChild, Ordering.isGE_iff_ne_lt, heapifyDown_eq_of_not_lt]

end heapifyDown

section heapifyUp

/-- heapifyUp fixes the heap when the only violation is at i
    and i's children are already ≤ i's parent -/
theorem heapifyUp_wf_bottomUp [Ord α] [Std.TransOrd α] [Std.OrientedOrd α]
    {a : Vector α sz} {i : Fin sz}
    (hexcept : WF.exceptAt a i)
    (hchildren : WF.childLeParent a i) :
    WF.bottomUp (heapifyUp a i) := by
  induction a, i using heapifyUp.induct with
  | case1 a =>
    simp only [heapifyUp]
    exact WF.bottomUp_of_exceptAt_zero a (by omega) hexcept
  | case2 a i hisucc j h_lt ih =>
    have h_le : compare a[j] a[i+1] |>.isLE := by simp_all [Ordering.isLE_eq_isLT_or_isEq]
    simp only [heapifyUp, h_lt, ↓reduceIte, j]
    apply ih
    · exact WF.exceptAt_swap a ⟨i+1, by omega⟩ h_le hexcept hchildren
    · exact WF.childLeParent_swap a ⟨i+1, by omega⟩ h_le hexcept
  | case3 a i hisucc j h_nlt =>
    simp_all only [heapifyUp, j]
    apply WF.bottomUp_of_exceptAt_and_parent a ⟨i+1, by omega⟩ hexcept
    apply WF.parent_of_isGE a ⟨i + 1, by omega⟩ <;> simp_all [Ordering.isGE_iff_ne_lt]

/-- `heapifyUp` restores the full heap property, given that all nodes except `i` satisfy
the parent property and `i`'s children are ≤ `i`'s parent. -/
theorem heapifyUp_wf [Ord α] [Std.TransOrd α] [Std.OrientedOrd α]
    {a : Vector α sz} {i : Fin sz} (hexcept : WF.exceptAt a i) (hchildren : WF.childLeParent a i) :
    WF.topDown (heapifyUp a i) := by
  rw [WF.iff_bottomUp]
  simp_all [heapifyUp_wf_bottomUp]

theorem heapifyUp_perm [Ord α] {a : Vector α sz} {i : Fin sz} :
    (heapifyUp a i).Perm a := by
  induction a, i using heapifyUp.induct
  all_goals
    unfold heapifyUp
    grind only [Vector.Perm.trans, Vector.swap_perm, heapifyUp, Vector.Perm.rfl]

end heapifyUp

section perm

/-- x :: l is a permutation of l ++ [x] -/
theorem List.cons_perm_append_singleton (x : α) (l : List α) : (x :: l).Perm (l ++ [x]) := by
  induction l with
  | nil => rfl
  | cons y ys ih => exact (List.Perm.swap y x ys).trans (ih.cons y)

/-- For a vector, the last element cons'd with pop.toList is a permutation of toList -/
theorem Vector.last_cons_pop_perm {v : Vector α (n+1)} :
    (v[n] :: v.pop.toList).Perm v.toList := by
  have hne : v.toList ≠ [] := by simp
  have hdrop : v.pop.toList = v.toList.dropLast := by
    rw [← Vector.toList_toArray]
    simp only [Vector.toArray_pop, Array.toList_pop, Vector.toList_toArray]
  have hlast : v[n] = v.toList.getLast hne := by
    simp [List.getLast_eq_getElem, Vector.length_toList, Vector.getElem_toList]
  rw [hdrop, hlast]
  apply List.cons_perm_append_singleton _ _ |>.trans
  rw [List.dropLast_concat_getLast hne]

@[simp]
theorem Vector.swap_same {v : Vector α n} {i : Nat} (hi : i < n) :
    v.swap i i hi hi = v := by
  ext k hk
  simp_all [Vector.getElem_swap]

/-- Swapping element i with the last and popping gives a permutation with v[i] prepended -/
theorem Vector.swap_last_pop_perm {v : Vector α (n+1)} {i : Fin (n+1)} (hi : i.val < n) :
    (v[i] :: (v.swap i n (by omega) (by omega) |>.pop).toList).Perm v.toList := by
  have h_swap_last : (v.swap i n (by omega) (by omega))[n] = v[i] :=
    Vector.getElem_swap_right (by omega) (by omega)
  rw [← h_swap_last]
  apply Vector.last_cons_pop_perm.trans
  exact (Vector.swap_perm (by omega) (by omega)).toList

/-- popMax returns a permutation: the original is a perm of max :: popMax -/
theorem popMax_perm [Ord α] {heap : BinaryHeap α} (h : 0 < heap.size) :
    (heap.arr[0] :: heap.popMax.arr.toList).Perm heap.arr.toList := by
  have hne : heap.size ≠ 0 := by omega
  unfold popMax
  simp only [hne, reduceDIte]
  split <;> rename_i hsz
  · have hdown := heapifyDown_perm (a := heap.vector.swap 0 (heap.size - 1) |>.pop) (i := ⟨0, hsz⟩)
    have hswap := Vector.swap_last_pop_perm (n := heap.size - 1)
      (v := heap.vector.cast (by omega)) (i := ⟨0, by omega⟩) (hi := by omega)
    simp only [vector, size]
    exact (hdown.toList.cons _).trans hswap
  · have : heap.size = 1 := by omega
    have hswap := Vector.last_cons_pop_perm (n := 0) (v := heap.vector.cast (by omega))
    simp_all [Vector.cast, vector, size]

/-- When max returns some, the value equals arr[0]. -/
theorem max_eq_arr_zero {heap : BinaryHeap α} {x : α} (h : heap.max = some x) :
    x = heap.arr[0]'(size_pos_of_max h) := by
  unfold max at h
  have := Array.getElem_eq_iff (x := x) (h := size_pos_of_max h)
  simp_all

/-- The inner loop of heapSort produces a permutation of heap ++ out -/
theorem heapSort_loop_perm [instOrd : Ord α] (heap : BinaryHeap α) (out : Array α) :
    (Array.heapSort.loop heap out).toList.Perm (heap.arr.toList ++ out.toList) := by
  unfold Array.heapSort.loop
  split
  · simp_all [size]
  · rename_i x h_some
    have h_pos : 0 < heap.size := size_pos_of_max h_some
    have h_x : x = heap.arr[0] := max_eq_arr_zero h_some
    apply heapSort_loop_perm heap.popMax (out.push x) |>.trans
    simp only [Array.toList_push]
    apply (List.perm_append_comm.append_left _).trans
    simp only [← List.append_assoc]
    apply List.Perm.append_right
    apply List.cons_perm_append_singleton x _ |>.symm.trans
    simp_all [popMax_perm]

theorem mkHeap.loop_perm [Ord α] {a : Vector α sz} {h : n ≤ sz} :
    (mkHeap.loop n a h).Perm a := by
  induction n generalizing a with
  | zero => simp [mkHeap.loop]
  | succ i ih =>
    simp only [mkHeap.loop]
    exact ih.trans heapifyDown_perm

end perm

/-- The inner loop of `mkHeap` establishes `WF.children` for all nodes, given that
nodes at index ≥ n already satisfy the invariant. -/
theorem mkHeap.loop_wf [Ord α] [Std.TransOrd α] [Std.OrientedOrd α]
    {n : Nat} {a : Vector α sz} {h : n ≤ sz}
    (hinv : ∀ k : Fin sz, n ≤ k.val → WF.children a k) :
    ∀ k : Fin sz, WF.children (mkHeap.loop n a h) k := by
  induction n generalizing a with
  | zero => simp_all [mkHeap.loop]
  | succ i ih =>
    have hi_lt : i < sz := by omega
    obtain ⟨hwf_at, hwf_below⟩:= heapifyDown_wf (a := a) (i := ⟨i, hi_lt⟩) hinv
    apply ih
    intro k hk
    by_cases hk_eq : k = i
    · grind only
    · exact hwf_below k (by omega : i < k)

public section

@[simp]
theorem size_empty : (@empty α).size = 0 := by
  simp [empty, size]

@[simp]
theorem size_singleton {x : α} : (singleton x).size = 1 := by
  simp [singleton, size]

@[simp, grind .]
theorem empty_wf [Ord α] : WF (empty : BinaryHeap α) := by
  simp [empty, WF, vector, WF.topDown_empty]

@[simp, grind .]
theorem singleton_wf [Ord α] {x : α} : WF (singleton x) := by
  simp [WF, singleton, vector, WF.topDown_singleton]

@[simp, grind .]
theorem mkHeap_wf [Ord α] [Std.TransOrd α] [Std.OrientedOrd α] {a : Vector α sz} :
    WF.topDown (mkHeap a) := by
  unfold mkHeap
  apply mkHeap.loop_wf
  intros
  constructor <;> intro <;> omega

theorem mkHeap_perm [instOrd : Ord α] {a : Vector α sz} : (mkHeap a).toList.Perm a.toList :=
  mkHeap.loop_perm |>.toList

@[simp]
theorem size_insert [Ord α] (heap : BinaryHeap α) (x : α) :
    (heap.insert x).size = heap.size + 1 := by
  simp [size, insert]

@[grind .]
theorem insert_wf [Ord α] [Std.TransOrd α] [Std.OrientedOrd α] {heap : BinaryHeap α}
    {x : α} (h_wf : heap.WF) :
    (heap.insert x).WF := by
  unfold insert
  apply WF.topDown_toArray
  rw [WF.iff_bottomUp]
  apply heapifyUp_wf_bottomUp
  . intro i _
    unfold WF at h_wf
    rw [WF.iff_bottomUp] at h_wf
    unfold WF.bottomUp at h_wf
    intro h_nz
    simp only [Fin.getElem_fin]
    rw [Vector.getElem_push_lt, Vector.getElem_push_lt]
    exact h_wf ⟨i.val, by grind only⟩ h_nz
  . grind only [WF.childLeParent]

theorem mem_insert [Ord α] {heap : BinaryHeap α} :
    y ∈ heap.insert x ↔ y = x ∨ y ∈ heap := by
  unfold insert
  simp only [mem_def, Vector.mem_toArray_iff]
  rw [Vector.Perm.mem_iff heapifyUp_perm]
  simp_all [vector, or_comm]

theorem mem_iff_get {heap : BinaryHeap α} :
    a ∈ heap ↔ ∃ i : Fin heap.size, heap.get i = a := by
  simp_all [mem_def, get, Array.mem_iff_getElem, size, Fin.exists_iff]

@[grind .]
theorem max_ge_all [Ord α] [Std.TransOrd α]
    {heap : BinaryHeap α} {y: α} (hwf : WF heap) (h_in: y ∈ heap) (h_ne : heap.size > 0) :
    let root := heap.max.get (by simp_all [max, size])
    compare root y |>.isGE := by
  obtain ⟨idx, h_sz, h_ge⟩ := Array.mem_iff_getElem.mp h_in
  have := WF.root_ge_all hwf h_ne ⟨idx, h_sz⟩
  simp_all [vector, max]

theorem popMax_wf [Ord α] [Std.TransOrd α] [Std.OrientedOrd α]
    {heap : BinaryHeap α} (h_wf : WF heap) :
    WF (heap.popMax) := by
  unfold popMax
  have htd : WF.topDown heap.vector := by simp_all [WF]
  simp only
  split
  . simp_all [WF]
  . split <;> apply WF.topDown_toArray
    . have hbelow : WF.below (heap.vector.swap 0 (heap.size - 1) (by omega) (by omega) |>.pop) 0 := by
        grind only [WF.below_swap_pop htd]
      simp_all [WF.topDown_iff_at_below_zero.mp, heapifyDown_wf (i := ⟨0, by omega⟩) hbelow]
    . grind only [WF.children, WF.topDown]

/-- Elements in popMax were in the original heap -/
theorem popMax_subset [Ord α] {heap : BinaryHeap α} {x : α} (h : x ∈ heap.popMax) :
    x ∈ heap := by
  have hperm := popMax_perm (heap := heap)
  by_cases h_sz : heap.size = 0
  · simp_all [popMax, mem_def]
  · have h_pos : 0 < heap.size := by omega
    have := (hperm h_pos).mem_iff (a := x)
    simp_all [mem_def]

theorem decreaseKey_wf [Ord α] [Std.TransOrd α] [Std.OrientedOrd α] {heap : BinaryHeap α}
    {i : Fin heap.size} (h_wf : WF heap) (h_leq : compare x (heap.get i) |>.isLE) :
    WF (heap.decreaseKey i x) := by
  unfold decreaseKey

  apply WF.topDown_toArray
  have htd : WF.topDown heap.vector := by simp_all [WF]

  have hbelow : WF.below (heap.vector.set i x i.isLt) i := WF.set_smaller_wf_below htd
  have ⟨hchildren_i, hbelow_i⟩ := heapifyDown_wf hbelow

  intro k
  rcases Nat.lt_trichotomy k.val i.val with hki | hki_eq | hik
  · by_cases hk_parent : k.val = (i.val - 1) / 2 ∧ 0 < i.val
    · have hk_eq : k = ⟨(i.val - 1) / 2, by omega⟩ := by ext; exact hk_parent.1
      rw [hk_eq]
      exact heapifyDown_preserves_wf_parent htd h_leq hk_parent.2
    · have : i.val ≠ 2 * k.val + 1 := by omega
      have : i.val ≠ 2 * k.val + 2 := by omega
      have : WF.children (heap.vector.set i x) k :=
              WF.set_preserves_wf_children_of_ne (htd k) (by omega) ‹_› ‹_›
      apply heapifyDown_preserves_wf_children_outside <;> assumption
  · exact Fin.ext hki_eq ▸ hchildren_i
  · exact hbelow_i k hik

@[grind .]
theorem increaseKey_wf [Ord α] [Std.TransOrd α] [Std.OrientedOrd α] {heap : BinaryHeap α}
    {i : Fin heap.size} (h_wf : WF heap) (h_ge : compare x (heap.get i) |>.isGE) :
    WF (heap.increaseKey i x) := by
  unfold increaseKey
  generalize hv : heap.vector = v
  have htd : WF.topDown v := by simp_all [WF]
  have hbu : WF.bottomUp v := by simpa [← WF.iff_bottomUp]
  have h_ge' : compare x v[i] |>.isGE := by simp_all [get, vector]
  apply WF.topDown_toArray
  rw [WF.iff_bottomUp]
  simp_all [WF.exceptAt_set_larger, WF.childLeParent_set_larger, heapifyUp_wf_bottomUp]

end
end BinaryHeap

public section
open Batteries.BinaryHeap

theorem Array.toBinaryHeap_wf [instOrd : Ord α] [Std.TransOrd α] [Std.OrientedOrd α]
    {a : Array α} :
    WF (a.toBinaryHeap) := by
  simp [WF.topDown_toArray, Array.toBinaryHeap]

theorem Vector.toBinaryHeap_wf [Ord α] [Std.TransOrd α] [Std.OrientedOrd α]
    {a : Vector α sz} :
    WF (Batteries.Vector.toBinaryHeap a) := by
  simp [WF.topDown_toArray, Vector.toBinaryHeap]

theorem Array.heapSort_perm [instOrd : Ord α] {a : Array α} :
    a.heapSort.toList.Perm a.toList := by
  apply heapSort_loop_perm
    (instOrd := instOrd.opposite)
    (Array.toBinaryHeap (instOrd := instOrd.opposite) a)
    #[] |>.trans
  simp only [List.append_nil]
  exact mkHeap_perm (instOrd := instOrd.opposite)

/-- The inner loop of heapSort produces a sorted list (descending in the Ord instance used). -/
private theorem heapSort_loop_sorted [instOrd : Ord α] [Std.TransOrd α] [Std.OrientedOrd α]
    (heap : BinaryHeap α) (out : Array α)
    (hwf : WF heap) (h_out_sorted : out.toList.Pairwise (compare · · |>.isGE))
    (h_heap_le_out : ∀ x ∈ heap, ∀ y ∈ out, compare x y |>.isLE) :
    (Array.heapSort.loop heap out).toList.Pairwise (compare · · |>.isGE) := by
  unfold Array.heapSort.loop
  split <;> try assumption
  rename_i x h
  have h_pos : 0 < heap.size := size_pos_of_max h
  apply heapSort_loop_sorted
  · exact popMax_wf hwf
  · have hx_in_heap : x ∈ heap := by
      simp_all [BinaryHeap.mem_def, BinaryHeap.max, Array.mem_of_getElem? h]
    rw [Array.toList_push, List.pairwise_append]
    refine ⟨by assumption, by simp, ?_⟩
    intros
    rw [Std.OrientedOrd.eq_swap, Ordering.isGE_swap]
    simp_all [Array.mem_toList_iff]
  · have hx_ge_heap : ∀ y ∈ heap, compare x y |>.isGE := by
      intro y hy
      have := max_ge_all hwf hy h_pos
      simp_all [Option.get_some]
    intro _ _ _ hy
    rw [Array.mem_push] at hy
    cases hy
    case' inr => rw [Std.OrientedOrd.eq_swap, Ordering.isLE_swap]
    all_goals simp_all [popMax_subset]

theorem Array.heapSort_sorted [instOrd : Ord α] [Std.TransOrd α] [Std.OrientedOrd α]
    {a : Array α} :
    a.heapSort.toList.Pairwise (compare · · |>.isLE) := by
  unfold Array.heapSort
  have h := heapSort_loop_sorted
    (instOrd := instOrd.opposite)
    (Array.toBinaryHeap (instOrd := instOrd.opposite) a)
    #[]
    (Array.toBinaryHeap_wf (instOrd := instOrd.opposite))
    (by simp)
    (by simp)
  apply List.Pairwise.imp _ h
  intro a b hge
  have : instOrd.opposite.compare a b = instOrd.compare b a := rfl
  rw [this, Std.OrientedOrd.eq_swap, Ordering.isGE_swap] at hge
  exact hge
end

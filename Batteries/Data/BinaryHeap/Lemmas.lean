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


/-! ### Utility lemmas -/
section Utility

theorem Ordering.isGE_of_swap_isLT [Ord α] [Std.OrientedOrd α]
    {x y : α} (hlt : compare x y |>.isLT) :
    compare y x |>.isGE := by
  rw [Std.OrientedOrd.eq_swap]
  simp_all

theorem List.cons_perm_append_singleton {l : List α} (x : α) : (x :: l).Perm (l ++ [x]) := by
  induction l with
  | nil => rfl
  | cons x' xs ih => exact List.Perm.swap x' x xs |>.trans (ih.cons x')

theorem Vector.last_cons_pop_perm {v : Vector α (n+1)} :
    (v[n] :: v.pop.toList).Perm v.toList := by
  have hne : v.toList ≠ [] := by simp
  have hdrop : v.pop.toList = v.toList.dropLast := by
    rw [← Vector.toList_toArray]
    simp only [Vector.toArray_pop, Array.toList_pop, Vector.toList_toArray]
  have hlast : v[n] = v.toList.getLast hne := by
    simp [List.getLast_eq_getElem, Vector.length_toList, Vector.getElem_toList]
  rw [hdrop, hlast]
  apply List.cons_perm_append_singleton _ |>.trans
  rw [List.dropLast_concat_getLast hne]

@[simp]
theorem Vector.swap_same {v : Vector α n} {i : Nat} (hi : i < n) :
    v.swap i i hi hi = v := by
  ext k hk
  simp_all [Vector.getElem_swap]

theorem Vector.swap_last_pop_perm {v : Vector α (n+1)} {i : Fin (n+1)} (hi : i.val < n) :
    (v[i] :: (v.swap i n (by omega) (by omega) |>.pop).toList).Perm v.toList := by
  simp only [Fin.getElem_fin]
  rw [← Vector.getElem_swap_right]
  apply Vector.last_cons_pop_perm.trans
  exact Vector.swap_perm (by omega) (by omega) |>.toList

end Utility

namespace Batteries.BinaryHeap

/-- If maxChild returns none, there are no children in bounds. -/
theorem maxChild_none_iff [Ord α] {a : Vector α sz} :
    maxChild a i = none ↔ sz ≤ 2 * i.val + 1 := by
  grind only [maxChild]

/-- maxChild returns some iff there is at least one child. -/
theorem maxChild_some_iff [Ord α] {a : Vector α sz} :
    (maxChild a i).isSome ↔ 2 * i.val + 1 < sz := by
  grind only [maxChild, = Option.isSome]

/-- If maxChild returns some j, then j is a child of i. -/
theorem maxChild_isChild [Ord α] {a : Vector α sz} (h : maxChild a i = some j) :
    j.val = 2 * i.val + 1 ∨ j.val = 2 * i.val + 2 := by
  grind only [maxChild, = Option.isSome]

theorem maxChild_ge_left [Ord α] [Std.OrientedOrd α] (a : Vector α sz) (i j : Fin sz)
    (hmc : maxChild a i = some j) (hleft : 2 * i.val + 1 < sz) :
    compare a[j] a[2 * i.val + 1] |>.isGE := by
  grind only [Ordering.isGE_of_swap_isLT, Ordering.isGE, Ordering.isLT, maxChild, Fin.getElem_fin]

theorem maxChild_ge_right [Ord α] [Std.OrientedOrd α] (a : Vector α sz)
    (i j : Fin sz) (hmc : maxChild a i = some j) (hright : 2 * i.val + 2 < sz) :
    compare a[↑j] a[2 * ↑i + 2] |>.isGE := by
  grind only [= Fin.getElem_fin, Ordering.isGE, Ordering.isLT, maxChild]

/-- After swapping with maxChild, `a[j]` (now at position `i`) dominates both children. -/
theorem WF.Children.of_swap_maxChild [Ord α] [Std.TransOrd α] {a : Vector α sz} {i j : Fin sz}
    (hmaxChild : maxChild a i = some j) (h_ge : (compare a[j] a[i]).isGE) :
    WF.Children (a.swap i j i.isLt j.isLt) i := by
  have hchild := maxChild_isChild hmaxChild
  constructor
  all_goals
    intro hside
    simp only [Fin.getElem_fin, Vector.getElem_swap_left]
    cases hchild
  case left.inl | right.inr => simp_all
  all_goals
    rw [Vector.getElem_swap_of_ne (by omega) (by omega)]
    first | apply maxChild_ge_left | apply maxChild_ge_right
    assumption

/-- If parent >= maxChild, then WF.Children holds at that position. -/
theorem WF.Children.of_ge_maxChild [Ord α] [Std.TransOrd α] {a : Vector α sz}
    (hmaxChild : maxChild a i = some j) (h_ge : (compare a[i] a[j]).isGE) :
    WF.Children a i := by
  constructor
    <;> intros
    <;> apply Std.TransOrd.isGE_trans h_ge
    <;> (first | apply maxChild_ge_left | apply maxChild_ge_right)
    <;> assumption

/-! ### heapifyDown related lemmas -/
section heapifyDown

/-- When maxChild returns none, heapifyDown is the identity. -/
@[simp]
theorem heapifyDown_eq_of_maxChild_none [Ord α] {a : Vector α sz} (h : maxChild a i = none) :
    heapifyDown a i = a := by
  grind only [heapifyDown]

/-- When maxChild returns some and the parent is less than the child,
  heapifyDown swaps and recurses. -/
theorem heapifyDown_eq_of_lt_child [Ord α] {a : Vector α sz}
    (hmaxChild : maxChild a i = some j) (h_lt : (compare a[i] a[j]).isLT) :
    heapifyDown a i = heapifyDown (a.swap i j i.isLt j.isLt) j := by
  grind only [heapifyDown]

/-- When maxChild returns some but parent is not less than child, heapifyDown is the identity. -/
theorem heapifyDown_eq_of_not_lt_child [Ord α] {a : Vector α sz}
    (hmaxChild : maxChild a i = some j) (h_not_lt : ¬(compare a[i] a[j]).isLT) :
    heapifyDown a i = a := by
  grind only [heapifyDown]

/-- `heapifyDown` does not modify elements outside the subtree rooted at `i`. -/
theorem heapifyDown_getElem_of_not_inSubtree [Ord α] {a : Vector α sz} {i : Fin sz}
    {k : Fin sz} (hnsub : ¬InSubtree i k) :
    (heapifyDown a i)[k] = a[k] := by
  induction a, i using heapifyDown.induct with
  | case1 => simp_all
  | case2 a i j hmc hij hlt ih =>
    have hnsub_j : ¬InSubtree j k := fun hsub_jk =>
      hnsub (InSubtree.of_child (maxChild_isChild hmc) |>.trans hsub_jk)
    rw [heapifyDown_eq_of_lt_child hmc hlt, ih hnsub_j]
    apply Vector.getElem_swap_of_ne <;> grind only [InSubtree]
  | case3 => simp_all [heapifyDown_eq_of_not_lt_child]

/-- Variant of `heapifyDown_getElem_of_not_inSubtree` that takes a `Nat` index instead of `Fin`
    Mostly for automation, simp/grind have a hard time doing this on their own -/
theorem heapifyDown_getElem_of_not_inSubtree' [Ord α] {a : Vector α sz} {i : Fin sz}
    (hk : k < sz) (hnsub : ¬InSubtree i k) :
    (heapifyDown a i)[k] = a[k] :=
  heapifyDown_getElem_of_not_inSubtree (k := ⟨k, hk⟩) hnsub

/-- heapifyDown at j preserves WF.Children k when i < k < j and j is a child of i -/
theorem heapifyDown_swap_children_of_lt [Ord α] {a : Vector α sz} {i j k : Fin sz}
    (hchild : j.val = 2 * i.val + 1 ∨ j.val = 2 * i.val + 2)
    (hik : i < k) (hkj : k < j) (hwf : WF.Children a k) :
    WF.Children (heapifyDown (a.swap i j i.isLt j.isLt) j) k := by
  apply WF.Children.congr hwf
    <;> intros
    <;> (try simp only [Fin.getElem_fin])
    <;> rw [heapifyDown_getElem_of_not_inSubtree' _ (by grind only [InSubtree.not_of_lt])]
    <;> apply Vector.getElem_swap_of_ne
    <;> omega

/-- `heapifyDown` preserves WF.Children at positions before the heapified index that are not its
  children. -/
-- possible to merge with above theorem? they have the exact same structure
theorem heapifyDown_get_of_not_child [Ord α] {v : Vector α sz}
    (hki : k < i) (hwf : WF.Children v k)
    (hleft_ne : i.val ≠ 2 * k.val + 1) (hright_ne : i.val ≠ 2 * k.val + 2) :
    WF.Children (heapifyDown v i) k := by
  apply WF.Children.congr hwf
    <;> intros
    <;> (try simp only [Fin.getElem_fin])
    <;> rw [heapifyDown_getElem_of_not_inSubtree' _ (by grind only [InSubtree.not_of_lt])]
    <;> rfl

/-- If v dominates all values in the subtree, v dominates the result at root -/
theorem heapifyDown_preserves_ge_root_of_subtree [Ord α] [Std.TransOrd α]
    {a : Vector α sz} (hge : ∀ k : Fin sz, InSubtree j.val k.val → (compare v a[k]).isGE) :
    (compare v (heapifyDown a j)[j]).isGE := by
  -- this proof isn't really inductive, heapifyDown.induct is just a convenient way to split the
  -- cases. 'split' doesn't work because of dependent rewriting issues.
  -- so you have to do e.g. cases maxChild a j and by_cases (compare a[j] a[i]).isLT manualy.
  -- Unsure if there is something more idiomatic.
  induction a, j using heapifyDown.induct with
  | case1 => simp_all [heapifyDown_eq_of_maxChild_none, InSubtree.refl]
  | case2 a j child hmaxChild _ h_lt _ =>
    have hchild_in_subtree := InSubtree.of_child (maxChild_isChild hmaxChild)
    rw [heapifyDown_eq_of_lt_child hmaxChild h_lt,
        heapifyDown_getElem_of_not_inSubtree <| InSubtree.not_of_lt <| maxChild_gt hmaxChild]
    simpa [Vector.getElem_swap_left] using hge child hchild_in_subtree
  | case3 => simp_all [heapifyDown_eq_of_not_lt_child, InSubtree.refl]

/-- heapifyDown at j preserves WF.Children at k when j is a child of k,
    k dominates everything in j's subtree, and WF.Children already holds at k -/
theorem heapifyDown_children_of_ge_subtree [Ord α] [Std.TransOrd α]
    {b : Vector α sz} {j k : Fin sz}
    (hj_child : j.val = 2 * k.val + 1 ∨ j.val = 2 * k.val + 2)
    (hge_subtree : ∀ m : Fin sz, InSubtree j.val m.val → (compare b[k] b[m]).isGE)
    (hwf_k : WF.Children b k) :
    WF.Children (heapifyDown b j) k := by
  have hk_not_sub : ¬InSubtree j k := InSubtree.not_of_lt (by omega)
  have ⟨hwf_l, hwf_r⟩ := hwf_k
  constructor
  all_goals
    intro hside
    simp only [heapifyDown_getElem_of_not_inSubtree hk_not_sub, Fin.getElem_fin]
    cases hj_child
  -- Matching cases: j is the child we're proving about
  case left.inl hj | right.inr hj =>
    simpa only [← hj] using heapifyDown_preserves_ge_root_of_subtree hge_subtree

  all_goals
    rw [heapifyDown_getElem_of_not_inSubtree' hside (by grind only [InSubtree.not_of_lt])]
    first | exact hwf_l hside | exact hwf_r hside

/-- heapifyDown at i preserves WF.Children at parent of i when value decreased -/
theorem heapifyDown_set_of_le_preserves_children [Ord α] [Std.TransOrd α] {v : Vector α sz}
    {i : Fin sz} (htd : WF.TopDown v) (h_ge : compare v[i] x |>.isGE) (hi : 0 < i.val) :
    WF.Children (heapifyDown (v.set i x i.isLt) i) ⟨(i.val - 1) / 2, by omega⟩ := by
  let parent : Fin sz := ⟨(i.val - 1) / 2, by omega⟩
  have h_parent_child : i.val = 2 * parent.val + 1 ∨ i.val = 2 * parent.val + 2 := by grind only
  have hparent : WF.Children v parent := htd parent
  apply heapifyDown_children_of_ge_subtree h_parent_child
  . grind only [Fin.getElem_fin, Vector.getElem_set_ne, htd.parent_ge_subtree_of_set]
  . apply hparent.set_of_ge_child h_parent_child
    grind only [WF.Children, Std.TransOrd.isGE_trans, Fin.getElem_fin]

theorem heapifyDown_children_swap [Ord α] [Std.TransOrd α] {a : Vector α sz} {i j : Fin sz}
    (hmaxChild : maxChild a i = some j) (h_ge : compare a[j] a[i] |>.isGE) (hbelow : WF.Below a i) :
    WF.Children (heapifyDown (a.swap i j i.isLt j.isLt) j) i := by
  have hchild := maxChild_isChild hmaxChild
  apply heapifyDown_children_of_ge_subtree hchild
  . intro m hsub
    simpa [Vector.getElem_swap_left] using
      WF.swap_preserves_ge_subtree (maxChild_gt hmaxChild) h_ge hbelow hsub
  . simpa using WF.Children.of_swap_maxChild hmaxChild h_ge

/-- `heapifyDown` restores the heap property at node `i` and below, given that all nodes
below `i` already satisfy `WF.Children`. -/
theorem heapifyDown_topDown [Ord α] [Std.TransOrd α] {a : Vector α sz} {i : Fin sz}
    (hbelow : WF.Below a i) :
    WF.Children (heapifyDown a i) i ∧ WF.Below (heapifyDown a i) i := by
  induction a, i using heapifyDown.induct with
  | case1 => grind only [heapifyDown_eq_of_maxChild_none, WF.Children, maxChild_none_iff]
  | case2 a i j hmaxChild h_ij h_lt ih =>
    rw [heapifyDown_eq_of_lt_child hmaxChild h_lt]
    have ⟨ih_at, ih_below⟩ := ih (hbelow.swap h_ij)
    have hchild := maxChild_isChild hmaxChild
    constructor
    -- (1) WF.Children at i: a[j] (now at i) dominates both children of i
    · exact heapifyDown_children_swap hmaxChild (Ordering.isGE_of_swap_isLT h_lt) hbelow
    -- (2) WF.Below at i: all nodes k > i satisfy WF.Children.
    -- Split by position of k relative to j (the node we recursed into):
    · intro k hik
      rcases Nat.lt_trichotomy j.val k.val with hlt | heq | hgt
      -- k < j: follows from ih
      · exact ih_below k hlt
      -- k = j: follows from ih
      · exact Fin.ext heq ▸ ih_at
      -- k > j and k > i: children of k between i and j satisfy property
      -- (not affected by heapify at j)
      · exact heapifyDown_swap_children_of_lt hchild (by omega) hgt (hbelow k hik)
  | case3 =>
    simp_all [heapifyDown_eq_of_not_lt_child, WF.Children.of_ge_maxChild, Ordering.isGE_iff_ne_lt]

end heapifyDown

/-! ### heapifyUp related lemmas -/
section heapifyUp

/-- heapifyUp fixes the heap when the only violation is at i
    and i's children are already ≤ i's parent -/
theorem heapifyUp_bottomUp [Ord α] [Std.TransOrd α] {a : Vector α sz}
    (h_exc : WF.ExceptAt a i) (h_clp : WF.ParentGeChildren a i) :
    WF.BottomUp (heapifyUp a i) := by
  induction a, i using heapifyUp.induct with
  | case1 =>
    simp only [heapifyUp]
    exact .of_exceptAt_root (by omega) h_exc
  | case2 a i hisucc j h_lt ih =>
    have h_ge := Ordering.isGE_of_swap_isLT h_lt
    simp only [heapifyUp, h_lt, ↓reduceIte, j]
    exact ih (h_exc.swap_parent h_ge h_clp) (.swap_parent h_ge h_exc)
  | case3 _ _ _ j =>
    simp_all only [heapifyUp, j]
    apply WF.BottomUp.of_parent_and_exceptAt h_exc
    intro
    simp_all [Ordering.isGE_iff_ne_lt]

/-- `heapifyUp` restores the full heap property, given that all nodes except `i` satisfy
the parent property and `i`'s children are ≤ `i`'s parent. -/
theorem heapifyUp_topDown [Ord α] [Std.TransOrd α]
    {a : Vector α sz} (hexcept : WF.ExceptAt a i) (hchildren : WF.ParentGeChildren a i) :
    WF.TopDown (heapifyUp a i) :=
  WF.TopDown.iff_bottomUp.mpr <| heapifyUp_bottomUp hexcept hchildren

end heapifyUp

/-! Other permutation related lemmas -/
section perm

/-- `heapifyDown` is a permutation -/
theorem heapifyDown_perm [Ord α] {a : Vector α sz} : (heapifyDown a i).Perm a := by
  induction a, i using heapifyDown.induct with
  | case1 => simp_all [heapifyDown_eq_of_maxChild_none]
  | case2 => simp_all [heapifyDown_eq_of_lt_child, Vector.Perm.trans ‹_›, Vector.swap_perm]
  | case3 => simp_all [heapifyDown_eq_of_not_lt_child]

/-- `heapifyUp` is a permutation -/
theorem heapifyUp_perm [Ord α] {a : Vector α sz} {i : Fin sz} : (heapifyUp a i).Perm a := by
  induction a, i using heapifyUp.induct
  all_goals
    unfold heapifyUp
    grind only [Vector.Perm.trans, Vector.swap_perm, Vector.Perm.refl]

/-- popMax returns a permutation: the original is a perm of max :: popMax -/
theorem popMax_perm [Ord α] {heap : BinaryHeap α} (h : 0 < heap.size) :
    (heap.arr[0] :: heap.popMax.arr.toList).Perm heap.arr.toList := by
  have hne : heap.size ≠ 0 := by omega
  unfold popMax
  simp only [hne, reduceDIte]
  split <;> rename_i hsz
  · apply heapifyDown_perm.toList.cons _ |>.trans
    apply Vector.swap_last_pop_perm (v := heap.vector.cast (by omega)) (i := ⟨0, by omega⟩)
    omega
  · simpa [show heap.size = 1 by omega]
      using Vector.last_cons_pop_perm (v := heap.vector.cast (by omega))

/-- When max returns some, the value equals arr[0]. -/
theorem max_eq_arr_zero [Ord α] {heap : BinaryHeap α} (h : heap.max = some x) :
    x = heap.arr[0]'(size_pos_of_max h) := by
  unfold max at h
  simp [Array.getElem_eq_iff.mpr h]

/-- The inner loop of toSortedArray produces a permutation of heap ++ out -/
theorem toSortedArray.loop_perm [Ord α] (heap : BinaryHeap α) (out : Array α) :
    (toSortedArray.loop heap out).toList.Perm (heap.arr.toList ++ out.toList) := by
  unfold toSortedArray.loop
  split
  · simp_all [size]
  · rename_i h_some
    rw [max_eq_arr_zero h_some]
    have hpos := size_pos_of_max h_some
    apply toSortedArray.loop_perm heap.popMax (out.push _) |>.trans
    simp only [Array.toList_push]
    apply List.perm_append_comm.append_left _ |>.trans
    simp only [← List.append_assoc]
    apply List.Perm.append_right
    apply List.cons_perm_append_singleton _ |>.symm.trans
    exact popMax_perm hpos

/-- `toSortedArray` produces a permutation of the heap. -/
theorem toSortedArray_perm [Ord α] (heap : BinaryHeap α) :
    heap.toSortedArray.Perm heap.arr := by
  apply Array.Perm.of_toList_perm
  apply toSortedArray.loop_perm heap #[] |>.trans
  simp

theorem mkHeap.loop_perm [Ord α] {a : Vector α sz} {h : n ≤ sz} :
    (mkHeap.loop n a h).Perm a := by
  induction n generalizing a with
  | zero => simp [mkHeap.loop]
  | succ _ ih => simp [mkHeap.loop, ih.trans heapifyDown_perm]

end perm

/-- The inner loop of `mkHeap` establishes `WF.Children` for all nodes, given that
nodes at index ≥ n already satisfy the invariant. -/
theorem mkHeap.loop_wf [Ord α] [Std.TransOrd α]
    {a : Vector α sz} {h : n ≤ sz} (hinv : ∀ k : Fin sz, n ≤ k.val → WF.Children a k) :
    WF.TopDown (mkHeap.loop n a h) := by
  intro
  induction n generalizing a with
  | zero => simp_all [mkHeap.loop]
  | succ i ih =>
    have hi_lt : i < sz := by omega
    have ⟨hwf_at, hwf_below⟩:= heapifyDown_topDown (i := ⟨i, hi_lt⟩) hinv
    apply ih
    intro k hk
    by_cases hk_eq : k = i
    · simpa [← hk_eq] using hwf_at
    · exact hwf_below k (show i < k by omega)

public section

@[simp]
theorem size_empty [Ord α] : (@empty α).size = 0 := by
  simp [empty, size]

@[simp]
theorem size_singleton [Ord α] {x : α} : (singleton x).size = 1 := by
  simp [singleton, size]

@[simp, grind .]
theorem empty_wf [Ord α] : WF (empty : BinaryHeap α) := by
  simp [empty, WF, vector]

@[simp, grind .]
theorem singleton_wf [Ord α] {x : α} : WF (singleton x) := by
  simp [WF, singleton, vector]

@[simp]
theorem max_empty [Ord α] : (empty : BinaryHeap α).max = none := by
  simp [empty, max]

@[simp]
theorem max_singleton [Ord α] {x : α} : (singleton x).max = some x := by
  simp [singleton, max]

/-- Constructing a heap from a vector produces a well-formed heap. -/
@[simp, grind .]
theorem mkHeap_wf [Ord α] [Std.TransOrd α] {a : Vector α sz} :
    WF.TopDown (mkHeap a) := by
  apply mkHeap.loop_wf
  grind only [WF.Children]

theorem mkHeap_perm [Ord α] {a : Vector α sz} : (mkHeap a).toArray.Perm a.toArray :=
  mkHeap.loop_perm |>.toArray

@[simp]
theorem size_insert [Ord α] (heap : BinaryHeap α) (x : α) :
    (heap.insert x).size = heap.size + 1 := by
  simp [size, insert]

theorem size_extractMax [Ord α] (heap : BinaryHeap α) :
    (heap.extractMax).2.size = heap.size - 1 := by
  simp [extractMax]

@[simp]
theorem extractMax_fst [Ord α] (heap : BinaryHeap α) :
    heap.extractMax.1 = heap.max := by simp [extractMax]

@[simp]
theorem extractMax_snd [Ord α] (heap : BinaryHeap α) :
    heap.extractMax.2 = heap.popMax := by simp [extractMax]

@[simp]
theorem size_decreaseKey [Ord α] (heap : BinaryHeap α) (i : Fin heap.size) (x : α) :
    (heap.decreaseKey i x).size = heap.size := by
  simp [decreaseKey, size]

@[simp]
theorem size_increaseKey [Ord α] (heap : BinaryHeap α) (i : Fin heap.size) (x : α) :
    (heap.increaseKey i x).size = heap.size := by
  simp [increaseKey, size]

@[grind .]
theorem insert_wf [Ord α] [Std.TransOrd α] {heap : BinaryHeap α} (h_wf : heap.WF) :
    (heap.insert x).WF := by
  apply WF.of_topDown
  apply heapifyUp_topDown
  . intro i _
    rw [WF, WF.TopDown.iff_bottomUp, WF.BottomUp] at h_wf
    intro h_nz
    simp only [Fin.getElem_fin]
    rw [Vector.getElem_push_lt, Vector.getElem_push_lt]
    exact h_wf ⟨i.val, by grind only⟩ h_nz
  . grind only [WF.ParentGeChildren]

@[simp]
theorem mem_empty [Ord α] {x : α} : ¬x ∈ empty := by
  simp [mem_def, empty]

@[simp]
theorem mem_singleton [Ord α] {x y : α} : x ∈ singleton y ↔ x = y := by
  simp [mem_def, singleton]

theorem mem_insert [Ord α] {heap : BinaryHeap α} :
    y ∈ heap.insert x ↔ y = x ∨ y ∈ heap := by
  simp only [insert, mem_def, Vector.mem_toArray_iff]
  rw [Vector.Perm.mem_iff heapifyUp_perm]
  simp_all [vector, or_comm]

theorem mem_iff_get [Ord α] {heap : BinaryHeap α} :
    a ∈ heap ↔ ∃ i : Fin heap.size, heap.get i = a := by
  simp_all [mem_def, get, Array.mem_iff_getElem, size, Fin.exists_iff]

@[grind .]
theorem max_ge_all [Ord α] [Std.TransOrd α]
    {heap : BinaryHeap α} {y: α} (hwf : WF heap) (h_in: y ∈ heap) (h_ne : heap.size > 0) :
    let root := heap.max.get (by simp_all [max, size])
    compare root y |>.isGE := by
  have ⟨idx, h_sz, h_ge⟩ := Array.mem_iff_getElem.mp h_in
  simpa [vector, max, h_ge] using hwf.toTopDown.root_ge_all h_ne ⟨idx, h_sz⟩

/-- Removing the maximum element from a well-formed heap preserves well-formedness. -/
theorem popMax_wf [Ord α] [Std.TransOrd α] {heap : BinaryHeap α} (h_wf : WF heap) :
    WF (heap.popMax) := by
  unfold popMax
  split
  . exact h_wf
  . split <;> apply WF.of_topDown
    . apply WF.TopDown.iff_root_and_below.mp
      exact heapifyDown_topDown (.of_topDown_swap_pop h_wf (by omega))
    . grind only [WF.Children, WF.TopDown]

/-- Replacing the maximum element in a well-formed heap preserves well-formedness. -/
theorem replaceMax_wf [Ord α] [Std.TransOrd α] {heap : BinaryHeap α} (h_wf : WF heap) :
    WF (heap.replaceMax x).2 := by
  unfold replaceMax
  split <;> apply WF.of_topDown
  · simp_all [WF.TopDown, WF.Children]
  · apply WF.TopDown.iff_root_and_below.mp
    exact heapifyDown_topDown (.of_topDown_set h_wf)

theorem insertExtractMax_wf [Ord α] [Std.TransOrd α] {heap : BinaryHeap α} (h_wf : WF heap) :
    WF (heap.insertExtractMax x).2 := by
  have htd : WF.TopDown heap.vector := by rwa [WF] at h_wf
  unfold insertExtractMax
  split
  · exact h_wf
  · split
    · apply WF.of_topDown
      apply WF.TopDown.iff_root_and_below.mp
      exact heapifyDown_topDown (.of_topDown_set htd)
    · exact h_wf

@[simp]
theorem size_insertExtractMax [Ord α] (heap : BinaryHeap α) (x : α) :
    (heap.insertExtractMax x).2.size = heap.size := by
  grind only [insertExtractMax, size, Vector.size_toArray]

theorem insertExtractMax_fst_of_empty [Ord α] {heap : BinaryHeap α} (h : heap.size = 0) (x : α) :
    (heap.insertExtractMax x).1 = x := by
  grind only [insertExtractMax, max_eq_none_iff]

theorem insertExtractMax_fst_of_lt [Ord α] {heap : BinaryHeap α}
    (hmax : heap.max = some m) (h_lt : (compare x m).isLT) :
    (heap.insertExtractMax x).1 = m := by
  grind only [insertExtractMax]

theorem insertExtractMax_fst_of_not_lt [Ord α] {heap : BinaryHeap α}
    (hmax : heap.max = some m) (h_nlt : ¬(compare x m).isLT) :
    (heap.insertExtractMax x).1 = x := by
  grind only [insertExtractMax]

@[simp]
theorem insertExtractMax_empty [Ord α] (x : α) :
    empty.insertExtractMax x = (x, empty) := by
  simp [insertExtractMax, empty, max]

@[simp]
theorem replaceMax_empty [Ord α] (x : α) :
    empty.replaceMax x = (none, singleton x) := by
  simp [replaceMax, empty, singleton, max, vector]

theorem size_replaceMax_of_empty [Ord α] {heap : BinaryHeap α} (h : heap.size = 0) (x : α) :
    (heap.replaceMax x).2.size = 1 := by
  grind only [replaceMax, size, Vector.size_toArray]

theorem size_replaceMax_of_nonempty [Ord α] {heap : BinaryHeap α} (h : heap.size ≠ 0) (x : α) :
    (heap.replaceMax x).2.size = heap.size := by
  unfold replaceMax size
  split <;> simp_all [max_eq_none_iff]

@[simp]
theorem replaceMax_fst [Ord α] (heap : BinaryHeap α) (x : α) :
    (heap.replaceMax x).1 = heap.max := by
  grind only [replaceMax, max_eq_none_iff.mpr]

@[simp]
theorem popMax_empty [Ord α] : (empty : BinaryHeap α).popMax = empty := by
  simp [popMax, empty, size]

@[simp]
theorem extractMax_empty [Ord α] : (empty : BinaryHeap α).extractMax = (none, empty) := by
  simp [extractMax]

/-- Elements in popMax were in the original heap -/
theorem mem_of_mem_popMax [Ord α] {heap : BinaryHeap α} {x : α} (h : x ∈ heap.popMax) :
    x ∈ heap := by
  by_cases h_sz : heap.size = 0
  · simp_all [popMax, mem_def]
  · have hmem := popMax_perm (heap := heap) (by omega) |>.mem_iff (a := x)
    simp_all [mem_def]

/-- Decreasing a key value in a well-formed heap and reheapifying downward preserves
  well-formedness. -/
theorem decreaseKey_wf [Ord α] [Std.TransOrd α] {heap : BinaryHeap α}
    {i : Fin heap.size} (h_wf : WF heap) (h_ge : compare (heap.get i) x |>.isGE) :
    WF (heap.decreaseKey i x) := by
  apply WF.of_topDown
  have htd : WF.TopDown heap.vector := by simp_all [WF]
  have hbelow : WF.Below (heap.vector.set i x _) i := WF.Below.of_topDown_set htd
  have ⟨hchildren_i, hbelow_i⟩ := heapifyDown_topDown hbelow
  intro k
  rcases Nat.lt_trichotomy k.val i.val with hki | hki_eq | hik
  · by_cases hk_parent : k.val = (i.val - 1) / 2 ∧ 0 < i.val
    · rw [show k = ⟨_, _⟩ from Fin.ext hk_parent.1]
      exact heapifyDown_set_of_le_preserves_children htd h_ge hk_parent.2
    · have hleft : i.val ≠ 2 * k.val + 1 := by omega
      have hright : i.val ≠ 2 * k.val + 2 := by omega
      apply heapifyDown_get_of_not_child hki _ hleft hright
      exact (htd k).set_of_ne (by omega) hleft hright
  · exact Fin.ext hki_eq ▸ hchildren_i
  · exact hbelow_i k hik

/-- Increasing a key value in a well-formed heap and reheapifying upward preserves well-formedness.
  -/
theorem increaseKey_wf [Ord α] [Std.TransOrd α] {heap : BinaryHeap α}
    {i : Fin heap.size} (h_wf : WF heap) (h_ge : compare x (heap.get i) |>.isGE) :
    WF (heap.increaseKey i x) :=
  have hbu : WF.BottomUp heap.vector := by rwa [WF, WF.TopDown.iff_bottomUp] at h_wf
  .of_topDown <|
    heapifyUp_topDown (.set_of_ge hbu h_ge) (.set_of_ge hbu h_ge)

/-- The inner loop of toSortedArray produces a sorted array -/
private theorem toSortedArray.loop_sorted [Ord α] [Std.TransOrd α] {heap : BinaryHeap α}
    {out : Array α} (hwf : WF heap) (h_out_sorted : out.toList.Pairwise (compare · · |>.isGE))
    (h_heap_le_out : ∀ x ∈ heap, ∀ y ∈ out, compare x y |>.isLE) :
    (toSortedArray.loop heap out).toList.Pairwise (compare · · |>.isGE) := by
  unfold toSortedArray.loop
  split <;> try assumption
  rename_i x h
  have h_pos : 0 < heap.size := size_pos_of_max h
  apply toSortedArray.loop_sorted
  · exact popMax_wf hwf
  · have : x ∈ heap := by simp_all [BinaryHeap.mem_def, BinaryHeap.max, Array.mem_of_getElem? h]
    rw [Array.toList_push, List.pairwise_append]
    refine ⟨by assumption, by simp, ?_⟩
    intros
    rw [Std.OrientedOrd.eq_swap]
    simp_all
  · have hx_ge_heap : ∀ y ∈ heap, compare x y |>.isGE := fun _ hy => by
      simpa [h] using max_ge_all hwf hy h_pos
    intro _ _ _ hy
    rw [Array.mem_push] at hy
    cases hy
    case' inr => rw [Std.OrientedOrd.eq_swap]
    all_goals simp_all [mem_of_mem_popMax]

/-- toSortedArray produces a sorted array if the heap is well-formed -/
theorem toSortedArray_sorted [Ord α] [Std.TransOrd α] {heap : BinaryHeap α} (hwf : WF heap) :
    heap.toSortedArray.toList.Pairwise (compare · · |>.isGE) := by
  simp_all [toSortedArray, toSortedArray.loop_sorted]

@[simp]
theorem size_toSortedArray [Ord α] {heap : BinaryHeap α} : heap.toSortedArray.size = heap.size :=
  toSortedArray_perm heap |>.size_eq

@[simp]
theorem mem_toSortedArray [Ord α] {heap : BinaryHeap α} {x : α} :
    x ∈ heap.toSortedArray ↔ x ∈ heap :=
  toSortedArray_perm heap |>.mem_iff

end
end BinaryHeap

public section
open Batteries.BinaryHeap

/-- Converting an array to a binary heap produces a well-formed heap. -/
theorem Array.toBinaryHeap_wf [Ord α] [Std.TransOrd α] {a : Array α} : WF (a.toBinaryHeap) := by
  simp [WF.of_topDown, Array.toBinaryHeap]

/-- Converting a vector to a binary heap produces a well-formed heap. -/
theorem Vector.toBinaryHeap_wf [Ord α] [Std.TransOrd α] {a : Vector α sz} :
    WF (Batteries.Vector.toBinaryHeap a) := by
  simp [WF.of_topDown, Vector.toBinaryHeap]

@[simp]
theorem Array.size_toBinaryHeap [Ord α] {a : Array α} : a.toBinaryHeap.size = a.size := by
  simp [Array.toBinaryHeap, BinaryHeap.size]

@[simp]
theorem Vector.size_toBinaryHeap [Ord α] {a : Vector α sz} :
    (Batteries.Vector.toBinaryHeap a).size = sz := by
  simp [Batteries.Vector.toBinaryHeap, BinaryHeap.size]

@[simp]
theorem Array.mem_toBinaryHeap [Ord α] {a : Array α} : x ∈ a.toBinaryHeap ↔ x ∈ a := by
  simp [Array.toBinaryHeap, BinaryHeap.mem_def, mkHeap_perm.mem_iff]

@[simp]
theorem Vector.mem_toBinaryHeap [Ord α] {a : Vector α sz} {x : α} :
    x ∈ Batteries.Vector.toBinaryHeap a ↔ x ∈ a := by
  simp only [Batteries.Vector.toBinaryHeap, BinaryHeap.mem_def, Vector.mem_toArray_iff]
  simp [← Vector.mem_toArray_iff, mkHeap_perm.mem_iff]

theorem Array.heapSort_perm [instOrd : Ord α] {a : Array α} : a.heapSort.Perm a := by
  letI := instOrd.opposite
  apply toSortedArray_perm a.toBinaryHeap |>.trans
  exact mkHeap_perm

@[simp]
theorem Array.size_heapSort [instOrd : Ord α] {a : Array α} : a.heapSort.size = a.size :=
  Array.heapSort_perm.size_eq

/-- `heapSort` produces a sorted array. -/
theorem Array.heapSort_sorted [instOrd : Ord α] [Std.TransOrd α] {a : Array α} :
    a.heapSort.toList.Pairwise (compare · · |>.isLE) := by
  letI := instOrd.opposite
  apply List.Pairwise.imp _ (toSortedArray_sorted Array.toBinaryHeap_wf)
  intro a b hge
  rw [Std.OrientedOrd.eq_swap] at hge
  simp_all [show instOrd.compare a b = instOrd.opposite.compare b a from rfl]

end

module
import all Batteries.Data.BinaryHeap.Basic
public import Batteries.Data.BinaryHeap.Basic
public import Batteries.Data.BinaryHeap.WF
import all Batteries.Data.BinaryHeap.WF

namespace Batteries.BinaryHeap


/-- If maxChild returns none, there are no children in bounds. -/
theorem maxChild_none_iff [Ord α] (a : Vector α sz) (i : Fin sz) :
    maxChild a i = none ↔ sz ≤ 2 * i.val + 1 := by
  grind only [maxChild]

/-- maxChild returns some iff there is at least one child. -/
theorem maxChild_some_iff [Ord α] (a : Vector α sz) (i : Fin sz) :
    (maxChild a i).isSome ↔ 2 * i.val + 1 < sz := by
  grind only [maxChild, = Option.isSome_none, = Option.isSome_some]

/-- If maxChild returns some j, then j is a child of i. -/
theorem maxChild_isChild [Ord α] (a : Vector α sz) (i : Fin sz) (j : Fin sz)
    (h : maxChild a i = some j) :
    j.val = 2 * i.val + 1 ∨ j.val = 2 * i.val + 2 := by
  grind only [maxChild, = Option.isSome_none, = Option.isSome_some]

/-- maxChild returns an index greater than i. -/
theorem maxChild_gt [Ord α] (a : Vector α sz) (i : Fin sz) (j : Fin sz)
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

/-- heapifyDown doesn't modify positions before the starting index. -/
theorem heapifyDown_preserves_prefix [Ord α] (a : Vector α sz) (i k : Fin sz) (hk : k < ↑i) :
    (heapifyDown a i)[k] = a[k] := by
  induction a, i using heapifyDown.induct <;> grind [heapifyDown]


section heapifyDown

/-- `heapifyDown` does not modify elements outside the subtree rooted at `i`. -/
theorem heapifyDown_get_of_not_inSubtree [Ord α] {a : Vector α sz} {i : Fin sz}
    {k : Fin sz} (hnsub : ¬InSubtree i k) :
    (heapifyDown a i)[k] = a[k] := by
  -- I cannot split on the result of the maxChild call inside of heapifyDown directly because of
  -- some dependence issue relating to getElem.
  -- this is a workaround
  cases hmc : maxChild a i
  all_goals unfold heapifyDown; conv => lhs; arg 1; simp only; rw [hmc]; simp only;

  rename_i j
  split <;> try rfl
  have hij : i < j := by grind only [maxChild_gt]

  have hnsub_j : ¬InSubtree j k := by
    grind only [InSubtree.not_of_lt, maxChild_isChild,
      InSubtree.lt_of_ne, InSubtree.trans, InSubtree]

  rw [heapifyDown_get_of_not_inSubtree hnsub_j]
  grind only [= Fin.getElem_fin, Vector.getElem_swap_of_ne, InSubtree]
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
    (hnsub_left : ∀ h : 2 * k.val + 1 < sz, ¬InSubtree i.val (2 * k.val + 1)
      := by grind only [InSubtree.not_of_lt])
    (hnsub_right : ∀ h : 2 * k.val + 2 < sz, ¬InSubtree i.val (2 * k.val + 2)
      := by grind only [InSubtree.not_of_lt])
    :
    WF.children (heapifyDown a i) k := by
  obtain ⟨hwf_left, hwf_right⟩ := hwf
  constructor
  case' left =>  let childIdx := 2 * k.val + 1
  case' right => let childIdx := 2 * k.val + 2
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

theorem heapifyDown_preserves_wf_children_outside [Ord α] {v : Vector α sz} {i k : Fin sz}
    (hki : k < i) (hwf : WF.children v k)
    (hleft_ne : 2 * k.val + 1 ≠ i.val) (hright_ne : 2 * k.val + 2 ≠ i.val) :
    WF.children (heapifyDown v i) k :=
  heapifyDown_preserves_wf_children_of_not_inSubtree
    (InSubtree.not_of_lt hki)
    rfl
    (fun _ => rfl)
    (fun _ => rfl)
    hwf

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
    simp_all only [Fin.getElem_fin]
    rw [Vector.getElem_set_ne (i := i.val) (j := parent.val) _ _ (by omega)]
    by_cases heq : childIdx = i.val
    · simp only [parent, heq, childIdx]
      exact heapifyDown_root_bounded (WF.parent_dominates_set_subtree htd h_le hi)
    . have hsub : ¬InSubtree i.val childIdx :=  by grind only [InSubtree.not_of_lt]
      rw [heapifyDown_get_of_not_inSubtree' hside hsub]
      rw [Vector.getElem_set_ne _ _ (by simp_all only [ne_eq]; omega)]
      simp_all [childIdx, parent]


/-- a[j] dominates everything in (a.swap i j)'s subtree at j when i < j and a[i] < a[j] -/
theorem swap_child_dominates [Ord α] [Std.TransOrd α] [Std.OrientedOrd α]
    {a : Vector α sz} {i j : Fin sz} (h_ij : i < j) (h_lt : (compare a[i] a[j]).isLT)
    (hbelow : WF.below a i) (k : Fin sz) (hsub : InSubtree j k) :
    (compare a[j] (a.swap i j)[k]).isGE := by
  by_cases hk_eq_j : k = j
  · unfold Ordering.isGE
    rw [Std.OrientedOrd.eq_swap]
    simp_all
  · have : (a.swap i j)[k] = a[k] := Vector.getElem_swap_of_ne
      (by grind only [InSubtree.not_of_lt])
      (by omega)
    simp_all [
      WF.root_ge_subtree j.isLt
      (hwf_at := hbelow j h_ij)
      (hwf_below := WF.below_mono (by omega) hbelow)
      (hsub := hsub)
    ]

theorem heapifyDown_wf [Ord α] [Std.TransOrd α] [Std.OrientedOrd α]
    {a : Vector α sz} {i : Fin sz}
    (hbelow : WF.below a i) :
    WF.children (heapifyDown a i) i ∧ WF.below (heapifyDown a i) i := by
  induction a, i using heapifyDown.induct with
  | case1 a i h => grind only [WF.children, WF.below, maxChild]
  | case2 a i j hmaxChild h_ij h_ai_aj ih =>
    obtain ⟨ih_at, ih_below⟩ := ih (WF.below_swap (hbelow := hbelow) (hij := h_ij))
    have hnsub_i : ¬InSubtree j.val i.val := InSubtree.not_of_lt h_ij
    have hchild := maxChild_isChild a i j hmaxChild

    have hchildren : WF.children (heapifyDown a i) i := by
      constructor

      all_goals
        intro hside
        unfold heapifyDown

        -- I cannot reduce the match statement inside heapifyDown directly via hmaxChild
        -- because of some dependence issue. This is a workaround
        simp only
        conv => lhs; arg 1; arg 1; arg 1; rw [hmaxChild]
        conv => lhs; arg 1; arg 2; arg 1; rw [hmaxChild]
        simp only [h_ai_aj, ↓reduceIte]

        simp only [heapifyDown_get_of_not_inSubtree hnsub_i, Fin.getElem_fin,
          Vector.getElem_swap_left]
        cases hchild
      case left.inl | right.inr =>
        grind only [Fin.getElem_fin,
          heapifyDown_root_bounded (swap_child_dominates h_ij h_ai_aj hbelow)]
      case left.inr =>
        have hnsub_l : ¬InSubtree j.val (2 * i.val + 1) := InSubtree.not_of_lt (by omega)
        grind only [Fin.getElem_fin, = Vector.getElem_swap,
          InSubtree, = maxChild_ge_left, heapifyDown_get_of_not_inSubtree' hside hnsub_l]
      case right.inl =>
        have hnsub_r : ¬InSubtree j.val (2 * i.val + 2) := by grind only [InSubtree.not_of_lt]
        grind only [Fin.getElem_fin, = Vector.getElem_swap,
          InSubtree, = maxChild_ge_right, heapifyDown_get_of_not_inSubtree' hside hnsub_r]

    have hbelow : WF.below (heapifyDown a i) i  := by
      unfold heapifyDown
      intro k
      split
      . grind only
      . cases Nat.lt_trichotomy j k <;> grind only [heapifyDown_swap_preserves_wf_children_of_lt,
        WF.children, WF.below, = Fin.getElem_fin]

    exact ⟨hchildren, hbelow⟩
  | case3 a i j hmaxChild hij h_lt =>
    have h_ge : (compare a[i] a[j]).isGE
      := by grind only [Ordering.isGE, Ordering.isLT]
    grind only [heapifyDown, WF.children, = Fin.getElem_fin,
      InSubtree.not_of_lt, !Std.TransOrd.isGE_trans, = maxChild_ge_left,
      = maxChild_ge_right]

end heapifyDown

section heapifyUp

/-- heapifyUp fixes the heap when the only violation is at i
    and i's children are already ≤ i's parent -/
theorem heapifyUp_wf_bottomUp [Ord α] [Std.TransOrd α] [Std.OrientedOrd α]
    (a : Vector α sz) (i : Fin sz)
    (hexcept : WF.exceptAt a i)
    (hchildren : WF.childLeParent a i) :
    WF.bottomUp (heapifyUp a i) := by
  induction a, i using heapifyUp.induct with
  | case1 a =>
    simp only [heapifyUp]
    exact WF.bottomUp_of_exceptAt_zero a (by omega) hexcept
  | case2 a i hisucc j h_lt ih =>
    have h_le : compare a[j] a[i+1] |>.isLE := by
      grind only [Ordering.isLT, Ordering.isLE, = Fin.getElem_fin]
    simp only [heapifyUp, h_lt, ↓reduceIte, j]
    apply ih
    · exact WF.exceptAt_swap a ⟨i+1, by omega⟩ h_le hexcept hchildren
    · exact WF.childLeParent_swap a ⟨i+1, by omega⟩ h_le hexcept
  | case3 a i hisucc j h_nlt =>
    simp_all only [heapifyUp, j]
    apply WF.bottomUp_of_exceptAt_and_parent a ⟨i+1, by omega⟩ hexcept
    exact WF.parent_of_isGE a
      ⟨i+1, by omega⟩
      (by grind only)
      (by grind only [Ordering.isLT, Ordering.isGE])

theorem heapifyUp_wf [Ord α] [Std.TransOrd α] [Std.OrientedOrd α]
    (a : Vector α sz) (i : Fin sz) (hexcept : WF.exceptAt a i) (hchildren : WF.childLeParent a i) :
    WF.topDown (heapifyUp a i) := by
  rw [WF.iff_bottomUp]
  simp_all [heapifyUp_wf_bottomUp]

end heapifyUp

theorem mkHeap.loop_wf [Ord α] [Std.TransOrd α] [Std.OrientedOrd α]
    (n : Nat) (a : Vector α sz) (h : n ≤ sz)
    (hinv : ∀ k : Fin sz, n ≤ k.val → WF.children a k) :
    ∀ k : Fin sz, WF.children (mkHeap.loop n a h) k := by
  induction n generalizing a with
  | zero => simp_all [mkHeap.loop]
  | succ i ih =>
    have hi_lt : i < sz := by omega
    obtain ⟨hwf_at, hwf_below⟩:= heapifyDown_wf (a := a) (i := ⟨i, hi_lt⟩) hinv
    have hinv' : ∀ k : Fin sz, i ≤ k.val → WF.children (heapifyDown a ⟨i, hi_lt⟩) k := by
      intro k hk
      by_cases hk_eq : k = i
      · grind only
      · have hlt : i < k := by omega
        exact hwf_below k hlt
    exact ih _ _ hinv'

public section

theorem mkHeap_wf [Ord α] [Std.TransOrd α] [Std.OrientedOrd α] (a : Vector α sz) :
    WF.topDown (mkHeap a) := by
  unfold mkHeap
  apply mkHeap.loop_wf
  intro _ _
  constructor
  all_goals
    intro _
    exfalso
    omega

theorem insert_wf [Ord α] [Std.TransOrd α] [Std.OrientedOrd α] (self : BinaryHeap α)
    (x : α) (h_wf : self.WF) :
    (self.insert x).WF := by
  unfold insert
  have h_sz : self.vector.size < (self.vector.push x).size := by grind only [size_insert]
  have h_ea : WF.exceptAt (self.vector.push x) ⟨self.vector.size, h_sz⟩ := by
    intro i _
    unfold WF at h_wf
    rw [WF.iff_bottomUp] at h_wf
    unfold WF.bottomUp at h_wf
    have : i < self.vector.size := by grind only
    intro h_nz
    grind [h_wf ⟨i.val, by omega⟩ h_nz]
  have h_clp : WF.childLeParent (self.vector.push x) ⟨self.vector.size, h_sz⟩ := by
    grind only [WF.childLeParent]
  simp only [WF, WF.iff_bottomUp]
  have := heapifyUp_wf_bottomUp (self.vector.push x) ⟨self.vector.size, h_sz⟩ h_ea h_clp
  rw [← Vector.mk_toArray (xs := (heapifyUp _ _))] at this
  grind only [vector, size]

/-- Correctness of max: it returns an element ≥ all elements in the heap -/
theorem max_ge_all [Ord α] [Std.TransOrd α] {self : BinaryHeap α} {hwf : WF self} {h : self.size > 0} :
    ∃ x, self.max = some x ∧ ∀ i : Fin self.size, (compare x ((self.get i))).isGE :=
  ⟨self.arr[0], by simp [max], (WF.max_ge_all hwf h ·)⟩

theorem max_eq_none_iff {self : BinaryHeap α} : self.max = none ↔ self.size = 0 := by
  simp [max, size]


theorem popMax_wf [Ord α] [Std.TransOrd α] [Std.OrientedOrd α]
    {self : BinaryHeap α} {h_wf : WF self} :
    WF (self.popMax) := by
  unfold popMax
  generalize hv : self.vector = v
  have htd : WF.topDown v := by simp_all [WF]
  simp only
  split
  . simp_all [WF]
  . split <;> apply WF.topDown_toArray
    . have hbelow : WF.below (v.swap 0 (v.size - 1) |>.pop) 0 := by
        grind only [WF.below_swap_pop htd]
      simp_all [WF.topDown_iff_at_below_zero.mp, heapifyDown_wf (i := ⟨0, by omega⟩) hbelow]
    . grind only [WF.children, WF.topDown]

theorem decreaseKey_wf [Ord α] [Std.TransOrd α] [Std.OrientedOrd α] {self : BinaryHeap α}
    {i : Fin self.size} {x : α} {h_leq : compare x (self.get i) |>.isLE} {h_wf : WF self} :
    WF (self.decreaseKey i x) := by
  unfold decreaseKey

  generalize hv : self.vector = v
  have htd : WF.topDown v := by simp_all [WF]
  have h_leq' : compare x v[i] |>.isLE := by
    have : self.size = self.arr.size := by simp [size]
    simp_all [get, ← hv, vector]

  apply WF.topDown_toArray

  have hbelow : WF.below (v.set i x) i := WF.set_smaller_wf_below htd
  have ⟨hchildren_i, hbelow_i⟩ := heapifyDown_wf hbelow

  intro k
  rcases Nat.lt_trichotomy k.val i.val with hki | hki_eq | hik
  · by_cases hk_parent : k.val = (i.val - 1) / 2 ∧ 0 < i.val
    · have hk_eq : k = ⟨(i.val - 1) / 2, by omega⟩ := by ext; exact hk_parent.1
      rw [hk_eq]
      exact heapifyDown_preserves_wf_parent htd h_leq' hk_parent.2
    · have hleft_ne : 2 * k.val + 1 ≠ i.val := by omega
      have hright_ne : 2 * k.val + 2 ≠ i.val := by omega
      have hwf_set : WF.children (v.set i x) k :=
              WF.set_preserves_wf_children_of_ne (htd k) (by omega) hleft_ne hright_ne
      exact heapifyDown_preserves_wf_children_outside hki hwf_set hleft_ne hright_ne
  · exact Fin.ext hki_eq ▸ hchildren_i
  · exact hbelow_i k hik
end

theorem increaseKey_wf [Ord α] [Std.TransOrd α] [Std.OrientedOrd α] {self : BinaryHeap α}
    {i : Fin self.size} {x : α} {h_ge : compare x (self.get i) |>.isGE} {h_wf : WF self} :
    WF (self.increaseKey i x) := by
  unfold increaseKey
  generalize hv : self.vector = v
  have htd : WF.topDown v := by simp_all [WF]
  have hbu : WF.bottomUp v := by rw [← WF.iff_bottomUp]; exact htd
  have h_ge' : compare x v[i] |>.isGE := by
    simp_all [get, ← hv, vector]
  apply WF.topDown_toArray
  rw [WF.iff_bottomUp]
  simp_all [WF.exceptAt_set_larger, WF.childLeParent_set_larger, heapifyUp_wf_bottomUp]


end BinaryHeap

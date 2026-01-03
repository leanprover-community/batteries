module
public import Batteries.Data.BinaryHeap
public section

namespace Batteries.BinaryHeap

--inductive WF.subtree [Ord α] (a : Vector α sz) : Nat → Prop
--  | leaf (i : Nat) (h : sz ≤ 2 * i + 1) : WF.subtree a i
--  | node (i : Nat) (hi : i < sz)
--         (hleft : 2 * i + 1 < sz → (compare a[i] a[2*i+1]).isGE)
--         (hright : 2 * i + 2 < sz → (compare a[i] a[2*i+2]).isGE)
--         (hwf_left : WF.subtree a (2*i+1))
--         (hwf_right : WF.subtree a (2*i+2))
--
--def WF' [Ord α] (a : Vector a sz) : Prop := WF.Subtree a 0

/-- Checks if the node at index `i` satisfies the max-heap property with respect to its children. -/
def WF.at [Ord α] (a : Vector α sz) (i : Fin sz) : Prop :=
  let left := 2 * i.val + 1
  let right := left + 1
  (∀ hleft : left < sz, compare a[i] a[left] |>.isGE) ∧
  (∀ hright : right < sz, compare a[i] a[right] |>.isGE)

def WF.below [Ord α] (a : Vector α sz) (i : Nat) : Prop
  := ∀ j : Fin sz, i < j.val → WF.at a j

/-- A `BinaryHeap` satisfies the max-heap property. -/
def WF [Ord α] (v : Vector α sz) : Prop
  := ∀ i : Fin sz, WF.at v i

/-- If maxChild returns none, there are no children in bounds. -/
theorem maxChild_none_iff [Ord α] (a : Vector α sz) (i : Fin sz)
  : maxChild a i = none ↔ sz ≤ 2 * i.val + 1
  := by grind [maxChild]

/-- maxChild returns some iff there is at least one child. -/
@[grind =]
theorem maxChild_some_iff [Ord α] (a : Vector α sz) (i : Fin sz)
  : (maxChild a i).isSome ↔ 2 * i.val + 1 < sz
  := by grind [maxChild]

/-- If maxChild returns some j, then j is a child of i. -/
@[grind .]
theorem maxChild_isChild [Ord α] (a : Vector α sz) (i : Fin sz) (j : Fin sz)
    (h : maxChild a i = some j)
  : j.val = 2 * i.val + 1 ∨ j.val = 2 * i.val + 2
  := by grind [maxChild]

/-- maxChild returns an index greater than i. -/
@[grind .]
theorem maxChild_gt [Ord α] (a : Vector α sz) (i : Fin sz) (j : Fin sz)
    (h : maxChild a i = some j) : i < j := by grind [maxChild]

@[grind]
inductive InSubtree (root : Nat) : Nat → Prop
  | refl : InSubtree root root
  | left : InSubtree root k → InSubtree root (2 * k + 1)
  | right : InSubtree root k → InSubtree root (2 * k + 2)


namespace InSubtree
@[grind .]
theorem le  (ins : InSubtree j k) : j ≤ k := by
  induction ins <;> omega


@[grind .]
theorem not_of_lt (hlt : k < j): ¬InSubtree j k := by
  intro hsub
  have := hsub.le
  omega

@[grind .]
theorem lt_of_ne (hsub : InSubtree j k) (hne : j ≠ k) : j < k := by grind [hsub.le]



@[grind .]
theorem trans (hij : InSubtree i j) (hjk : InSubtree j k) : InSubtree i k := by
  induction hjk with
  | refl => exact hij
  | left _ ih => exact InSubtree.left ih
  | right _ ih => exact InSubtree.right ih
end InSubtree


@[grind =]
private theorem maxChild_ge_left [Ord α] [Std.OrientedOrd α] (a : Vector α sz) (i j : Fin sz)
    (hmc : maxChild a i = some j) (hleft : 2 * i.val + 1 < sz)
  : compare a[↑j] a[2 * ↑i + 1] |>.isGE
  := by grind [Std.OrientedOrd.eq_swap, Ordering.swap_lt, Ordering.isGE, Ordering.isLT, maxChild]

@[grind =]
private theorem maxChild_ge_right [Ord α] [Std.OrientedOrd α] (a : Vector α sz) (i j : Fin sz)
    (hmc : maxChild a i = some j) (hright : 2 * i.val + 2 < sz)
  : compare a[↑j] a[2 * ↑i + 2] |>.isGE
  := by grind [Std.OrientedOrd.eq_swap, Ordering.swap_lt, Ordering.isGE, Ordering.isLT, maxChild]

/-- heapifyDown doesn't modify positions before the starting index. -/
@[grind=]
theorem heapifyDown_preserves_prefix [Ord α] (a : Vector α sz) (i k : Fin sz)
    (hk : k < ↑i)
  : (heapifyDown ↑a ↑i)[↑k] = a[↑k]
  := by induction a, i using heapifyDown.induct <;> grind [heapifyDown]

/-- WF.below is monotone: larger threshold means weaker condition. -/
theorem WF.below_mono {a : Vector α sz} {i j : Nat}  [Ord α]
    (hij : i ≤ j) (hbelow : WF.below a i)
  : WF.below a j
  := by grind [WF.below]

/-- The value at position i after heapifyDown is some value from the original subtree. -/
theorem WF.below_swap [Ord α] {a : Vector α sz} {i j : Fin sz}
    {hbelow : WF.below a i} {hij : i < j}
  : WF.below (a.swap ↑i ↑j) ↑j
  := by
    intro k hk_gt_j
    have hk_gt_i : i.val < k.val := Nat.lt_trans ‹_› ‹_›
    obtain ⟨_, _⟩ := hbelow k hk_gt_i
    grind [WF.at]


theorem WF.root_ge_subtree [Ord α] [Std.TransOrd α] [Std.ReflOrd α]
    {a : Vector α sz} {j : Nat} (hj : j < sz) {hwf_at : WF.at a ⟨j, hj⟩}
    {hwf_below : WF.below a j} {k : Nat} {hk : k < sz} {hsub : InSubtree j k}
  : (compare a[j] a[k]).isGE
  := by
    induction hsub
    case refl => grind [Std.ReflOrd.isLE_rfl, Ordering.isGE]
    all_goals
      obtain ⟨hwf_m, _⟩ : WF.at a ⟨‹_›, by omega⟩ := by grind [WF.below]
      grind [Std.TransOrd.isGE_trans, WF.at]

/-- heapifyDown doesn't modify positions outside the starting subtree -/
theorem heapifyDown_get_of_not_inSubtree [Ord α] {a : Vector α sz} {i : Fin sz}
    {k : Fin sz} (hnsub : ¬InSubtree i k)
  : (heapifyDown a ↑i)[↑k] = a[↑k]
  := by
    cases hmc : maxChild a i
    -- surely there's a better way to eliminate this dependent match?
    all_goals unfold heapifyDown; conv => lhs; arg 1; simp only; rw [hmc]; simp only;
    rename_i j
    split <;> try rfl
    have hij : i < j := by grind
    have hnsub_j : ¬InSubtree j k := by grind
    rw [heapifyDown_get_of_not_inSubtree hnsub_j]
    grind [Vector.getElem_swap_of_ne]
termination_by sz - i

theorem heapifyDown_get_of_not_inSubtree' [Ord α] {a : Vector α sz} {i : Fin sz}
    {k : Nat} (hk : k < sz)
    (hnsub : ¬InSubtree i k)
    : (heapifyDown a i)[k] = a[k]
  := heapifyDown_get_of_not_inSubtree (k := ⟨k, hk⟩) hnsub

/-- heapifyDown at j preserves WF.at k when i < k < j and j is a child of i -/
theorem heapifyDown_preserves_wf_at_of_lt [Ord α] {a : Vector α sz} {i j k : Fin sz}
    (hchild : j.val = 2 * i.val + 1 ∨ j.val = 2 * i.val + 2)
    (hik : i.val < k.val) (hkj : k.val < j.val)
    (hwf : WF.at a k)
  : WF.at (heapifyDown (a.swap ↑i ↑j) ↑j) ↑k
  := by
    obtain ⟨hwf_left, hwf_right⟩ := hwf
    have hnsub_k : ¬InSubtree j k := by grind only [InSubtree.not_of_lt]
    have hnsub_l : ¬InSubtree j (2 * k + 1) := by grind only [InSubtree.lt_of_ne, InSubtree.not_of_lt]
    have hnsub_r : ¬InSubtree j (2 * k + 2) := by grind only [InSubtree.lt_of_ne, InSubtree.not_of_lt]
    have : (a.swap i j)[k] = a[k] := Vector.getElem_swap_of_ne (by omega) (by omega)
    constructor <;> grind only [heapifyDown_get_of_not_inSubtree, heapifyDown_get_of_not_inSubtree',
      InSubtree.le, InSubtree.trans, InSubtree.not_of_lt, InSubtree.right, InSubtree.left,
      InSubtree.refl, = Vector.getElem_swap, Fin.getElem_fin]

/-- If v dominates all values in the subtree, v dominates the result at root -/
theorem heapifyDown_root_bounded [Ord α] [Std.TransOrd α] [Std.ReflOrd α]
    {a : Vector α sz} {j : Fin sz} {v : α}
    (hge : ∀ k : Fin sz, InSubtree j.val k.val → (compare v a[k]).isGE)
  : (compare v (heapifyDown a j)[j]).isGE := by grind [heapifyDown]


/-- a[j] dominates everything in (a.swap i j)'s subtree at j when i < j and a[i] < a[j] -/
theorem swap_child_dominates [Ord α] [Std.TransOrd α] [Std.OrientedOrd α] [Std.ReflOrd α]
    {a : Vector α sz} {i j : Fin sz}
    (h_ij : i < j)
    (h_lt : (compare a[i] a[j]).isLT)
    (hbelow : WF.below a i)
    (k : Fin sz) (hsub : InSubtree ↑j ↑k)
  : (compare a[j] (a.swap i j)[k]).isGE
  := by
    by_cases hk_eq_j : ↑k = ↑j
    · unfold Ordering.isGE
      rw [Std.OrientedOrd.eq_swap]
      simp_all
    · skip
      have : (a.swap ↑i ↑j)[↑k] = a[↑k] := by grind [Vector.getElem_swap_of_ne]
      simp only [this]
      exact WF.root_ge_subtree j.isLt
        (hwf_at := hbelow j h_ij)
        (hwf_below := WF.below_mono (by omega) hbelow)
        (hsub := hsub)

theorem heapifyDown_wf [Ord α] [Std.TransOrd α] [Std.OrientedOrd α] [Std.ReflOrd α] {a : Vector α sz} {i : Fin sz}
    (hbelow : WF.below a i.val)
  : WF.at (heapifyDown a i) i ∧ WF.below (heapifyDown a i) i.val
  := by
    induction a, i using heapifyDown.induct with
    | case1 a i h => grind only [WF.at, WF.below, maxChild]
    | case2 a i j hmaxChild h_ij h_ai_aj ih =>
      obtain ⟨ih_at, ih_below⟩ := ih (WF.below_swap (hbelow := hbelow) (hij := h_ij))
      have hnsub_i : ¬InSubtree j.val i.val := InSubtree.not_of_lt h_ij
      have hchild := maxChild_isChild a i j hmaxChild
      have : WF.below (heapifyDown a i) i  := by
        unfold heapifyDown
        intro k
        split
        . grind
        . cases Nat.lt_trichotomy j k <;> grind [heapifyDown_preserves_wf_at_of_lt, WF.at, WF.below]
      have : WF.at (heapifyDown a i) i := by
        unfold WF.at
        constructor
        all_goals
          intro hside
          conv => lhs; arg 1; unfold heapifyDown; arg 1; arg 1; simp only; rw[hmaxChild]; simp
          [hmaxChild, h_ai_aj, reduceIte, ←Fin.getElem_fin]
          conv => lhs; arg 1; arg 2; arg 1; simp only; rw[hmaxChild]; simp [hmaxChild, h_ai_aj,
          reduceIte, ←Fin.getElem_fin]
          simp [heapifyDown_get_of_not_inSubtree hnsub_i]
          cases hchild
        case left.inl | right.inr =>
          grind [heapifyDown_root_bounded (swap_child_dominates h_ij h_ai_aj hbelow)]
        case left.inr =>
          have hnsub_l : ¬InSubtree j.val (2 * i.val + 1) := by grind only [InSubtree.not_of_lt]
          grind [heapifyDown_get_of_not_inSubtree' hside hnsub_l]
        case right.inl =>
          have hnsub_r : ¬InSubtree j.val (2 * i.val + 2) := by grind only [InSubtree.not_of_lt]
          grind [heapifyDown_get_of_not_inSubtree' hside hnsub_r]
      simp_all
    | case3 a i j hmaxChild hij h_lt =>
      have h_ge : (compare a[i] a[j]).isGE := by grind [Std.OrientedOrd.eq_swap, Ordering.isGE, Ordering.isLT]
      grind [WF, Std.TransOrd.isGE_trans, heapifyDown, WF.at]

theorem mkHeap.loop_wf [Ord α] [Std.TransOrd α] [Std.OrientedOrd α] [Std.ReflOrd α]
    (n : Nat) (a : Vector α sz) (h : n ≤ sz)
    (hinv : ∀ k : Fin sz, n ≤ k.val → WF.at a k)
    : ∀ k : Fin sz, WF.at (mkHeap.loop n a h) k
  := by
    induction n generalizing a with
    | zero =>
      grind [mkHeap.loop]
    | succ i ih =>
      have hi_lt : i < sz := by omega
      obtain ⟨hwf_at, hwf_below⟩:= heapifyDown_wf (a := a) (i := ⟨i, hi_lt⟩) hinv
      have hinv' : ∀ k : Fin sz, i ≤ k.val → WF.at (heapifyDown a ⟨i, hi_lt⟩) k := by
        intro k hk
        by_cases hk_eq : k = i
        · grind
        · have hlt : i < k := by omega
          exact hwf_below k hlt
      exact ih _ _ hinv'

theorem mkHeap_wf [Ord α] [Std.TransOrd α] [Std.OrientedOrd α] [Std.ReflOrd α]
    (a : Vector α sz)
  : WF (mkHeap a) k
  := by grind [mkHeap, mkHeap.loop_wf, WF.at, WF]
end BinaryHeap

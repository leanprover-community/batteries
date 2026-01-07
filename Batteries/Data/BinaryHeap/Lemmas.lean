module
import all Batteries.Data.BinaryHeap.Basic
public import Batteries.Data.BinaryHeap.Basic

namespace Batteries.BinaryHeap

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
theorem lt_of_ne (hsub : InSubtree j k) (hne : j ≠ k) : j < k := by grind only [hsub.le]

@[grind .]
theorem trans (hij : InSubtree i j) (hjk : InSubtree j k) : InSubtree i k := by
  induction hjk with grind only [InSubtree]
end InSubtree


/-- The primary local correctness property for the heap. A node should be >= both its children
    (if it has them).
-/
@[expose]
public def WF.children [Ord α] (a : Vector α sz) (i : Fin sz) : Prop :=
  let left := 2 * i.val + 1
  let right := left + 1
  (∀ _ : left < sz, compare a[i] a[left] |>.isGE) ∧
  (∀ _ : right < sz, compare a[i] a[right] |>.isGE)

/-- The vector underlying a `BinaryHeap` is well-formed iff every node is ≥ any children it has -/
@[expose]
public def WF [Ord α] (v : Vector α sz) : Prop :=
  ∀ i : Fin sz, WF.children v i

namespace WF
variable {α : Type w} {sz : Nat}
/-- All nodes at indices greater than `i` are well-formed (according to WF.children)
    Used when verifying `heapifyDown`
-/
def below [Ord α] (a : Vector α sz) (i : Nat) : Prop :=
  ∀ j : Fin sz, i < j.val → WF.children a j

/-- WF.below is monotone: larger threshold means weaker condition. -/
theorem below_mono {a : Vector α sz} {i j : Nat}  [Ord α]
    (hij : i ≤ j) (hbelow : WF.below a i) : WF.below a j := by
  grind only [WF.below]

/-- if i < j, and the heap is well formed below i, then a[i] and a[j] can be swapped
  and the heap will still be well-formed below j
  --/
theorem below_swap [Ord α] {a : Vector α sz} {i j : Fin sz}
    {hbelow : WF.below a i} {hij : i < j} :
    WF.below (a.swap i j) j := by
  intro k hk_gt_j
  have hk_gt_i : i.val < k.val := Nat.lt_trans ‹_› ‹_›
  obtain ⟨_, _⟩ := hbelow k hk_gt_i
  constructor <;> grind only [= Fin.getElem_fin, = Vector.getElem_swap]


theorem root_ge_subtree [Ord α] [Std.TransOrd α]
    {a : Vector α sz} {j : Nat} (hj : j < sz) {hwf_at : WF.children a ⟨j, hj⟩}
    {hwf_below : WF.below a j} {k : Nat} {hk : k < sz} {hsub : InSubtree j k} :
    (compare a[j] a[k]).isGE := by
  induction hsub
  case refl => grind only [Ordering.isGE]
  all_goals
    obtain ⟨hwf_m, _⟩ : WF.children a ⟨‹_›, by omega⟩ := by grind [WF.below]
    grind only [= Fin.getElem_fin, !Std.TransOrd.isGE_trans]

/-- "Dual" correctness property to WF.children. A node should be <= its parent
    Used when verifying heapifyUp -/
def parent [Ord α] (a : Vector α sz) (i : Fin sz) : Prop :=
  ∀ _ : 0 < i.val, compare a[i] a[(i.val - 1)/2] |>.isLE

/-- The comparison gives us the parent property -/
theorem parent_of_isGE [Ord α] [Std.OrientedOrd α] (a : Vector α sz) (i : Fin sz) (hi : 0 < i.val)
    (h : compare a[(i.val - 1) / 2] a[i] |>.isGE) :
    WF.parent a i := by
  grind only [Std.OrientedOrd.eq_swap, !Ordering.isGE_swap, WF.parent]

/-- The children of node `i` are <= node `i`'s parent
    Part of the invariant required/maintained by heapifyUp
-/
def childLeParent [Ord α] (a: Vector α sz) (i : Fin sz) : Prop :=
  let parent := (i.val - 1) / 2
  let left := 2 * i.val + 1
  let right := left + 1
  (∀ _ : left < sz, compare a[left] a[parent] |>.isLE) ∧
  (∀ _ : right < sz, compare a[right] a[parent] |>.isLE)


/-- Every other node (except possibly i) is <= its parent (if it has one)
    Part of the invariant required/maintained by heapifyUp
-/
def exceptAt [Ord α] (a : Vector α sz) (i : Fin sz) : Prop :=
  ∀ j : Fin sz, i ≠ j → WF.parent a j

/-- If exceptAt i and childLeParent i, swap preserves exceptAt at parent -/
theorem exceptAt_swap [Ord α] [Std.TransOrd α] [Std.OrientedOrd α]
    (a : Vector α sz) (i : Fin sz)
    (h_le : compare a[(i.val - 1) / 2] a[i] |>.isLE)
    (hexcept : WF.exceptAt a i)
    (hchildren : WF.childLeParent a i) :
    WF.exceptAt (a.swap i ((i.val - 1) / 2)) ⟨(i.val - 1) / 2, by omega⟩ := by
  intro k hkj hk_pos
  by_cases hki : k.val = i.val
  · have : (i.val - 1) / 2 ≠ i := by omega
    simp_all
  · by_cases hk_child_of_i : (k.val - 1) / 2 = i.val
    · obtain ⟨hleft, hright⟩ := hchildren
      have hk_is_child : k.val = 2 * i.val + 1 ∨ k.val = 2 * i.val + 2 := by omega
      have hk_ne_parent : k.val ≠ (i.val - 1) / 2 := by omega
      rcases hk_is_child with hk_left | hk_right
      · have : 2 * i.val + 1 < sz := by omega
        simp_all
      · have : 2 * i.val + 2 < sz := by omega
        simp_all
    · unfold exceptAt parent at *
      grind only [Fin.ext_iff, Fin.isLt, = Fin.getElem_fin, = Vector.getElem_swap,
        !Std.TransOrd.isLE_trans]

/-- If exceptAt a i, swap preserves childLeParent at parent -/
theorem childLeParent_swap [Ord α] [Std.TransOrd α] [Std.OrientedOrd α]
    (a : Vector α sz) (i : Fin sz)
    (h_le : compare a[(i.val - 1) / 2] a[i] |>.isLE)
    (hexcept : WF.exceptAt a i) :
    WF.childLeParent (a.swap i ((i.val - 1) / 2)) ⟨(i.val - 1) / 2, by omega⟩ := by
  unfold WF.childLeParent at *
  let j := (i.val - 1) / 2
  constructor
  case' left  => let targetIdx := 2 * j + 1
  case' right => let targetIdx := 2 * j + 2
  all_goals
    intro hside
    unfold WF.exceptAt WF.parent at hexcept
    by_cases hli : targetIdx = i.val
    · have hji : j ≠ i.val := by omega
      grind only [= Fin.getElem_fin, = Vector.getElem_swap]
    · have hparent_eq : (targetIdx - 1) / 2 = j := by omega
      have h1 := hexcept ⟨targetIdx, hside⟩ (by grind only [Fin.ext_iff]) (by grind only)
      by_cases hj_pos : 0 < j <;>
        grind only [= Fin.getElem_fin, = Vector.getElem_swap, !Std.TransOrd.isLE_trans]

/- Dual global correctness property to `WF`. The vector underlying a BinomialHeap is well-formed
  iff all nodes are ≤ their parent.
  Used when verifying heapifyUp.
-/
def bottomUp [Ord α] (v : Vector α sz) : Prop :=
  ∀ i : Fin sz, WF.parent v i

/- WF and WF.bottomUp are equivalent -/
theorem iff_bottomUp [Ord α] [Std.OrientedOrd α] (a : Vector α sz) :
    WF a ↔ WF.bottomUp a := by
  constructor
  · intro hTop i
    have := hTop ⟨(i.val - 1) / 2, by omega⟩
    grind only [Ordering.isGE_swap, Std.OrientedOrd.eq_swap, WF.children,
      WF.parent, = Fin.getElem_fin]
  · intro hBottom i
    constructor <;> intro hchild
    case' mpr.left => have := hBottom ⟨2 * i.val + 1, hchild⟩
    case' mpr.right => have := hBottom ⟨2 * i.val + 2, hchild⟩
    all_goals grind only [Std.OrientedOrd.eq_swap, parent, = Fin.getElem_fin,
      !Ordering.isGE_swap]

/-- If exception is at 0, then bottomUp holds -/
theorem bottomUp_of_exceptAt_zero [Ord α] (a : Vector α sz) (h : 0 < sz)
    (hexcept : WF.exceptAt a ⟨0, h⟩) :
    WF.bottomUp a := by
  grind only [WF.parent, Fin.ext_iff, WF.bottomUp, WF.exceptAt]

/-- If parent property holds at i and exceptAt i, then bottomUp -/
theorem bottomUp_of_exceptAt_and_parent [Ord α] (a : Vector α sz) (i : Fin sz)
    (hexcept : WF.exceptAt a i) (hparent : WF.parent a i) :
    WF.bottomUp a := by
  grind only [bottomUp, parent, exceptAt]

end WF


/-- If maxChild returns none, there are no children in bounds. -/
theorem maxChild_none_iff [Ord α] (a : Vector α sz) (i : Fin sz) :
    maxChild a i = none ↔ sz ≤ 2 * i.val + 1 := by
  grind only [maxChild]

/-- maxChild returns some iff there is at least one child. -/
@[grind =]
theorem maxChild_some_iff [Ord α] (a : Vector α sz) (i : Fin sz) :
    (maxChild a i).isSome ↔ 2 * i.val + 1 < sz := by
  grind only [maxChild, = Option.isSome_none, = Option.isSome_some]

/-- If maxChild returns some j, then j is a child of i. -/
@[grind .]
theorem maxChild_isChild [Ord α] (a : Vector α sz) (i : Fin sz) (j : Fin sz)
    (h : maxChild a i = some j) :
    j.val = 2 * i.val + 1 ∨ j.val = 2 * i.val + 2 := by
  grind only [maxChild, = Option.isSome_none, = Option.isSome_some]

/-- maxChild returns an index greater than i. -/
@[grind .]
theorem maxChild_gt [Ord α] (a : Vector α sz) (i : Fin sz) (j : Fin sz)
    (h : maxChild a i = some j) : i < j := by
  grind only [maxChild, Lean.Grind.toInt_fin]


@[grind =]
private theorem maxChild_ge_left [Ord α] [Std.OrientedOrd α] (a : Vector α sz) (i j : Fin sz)
    (hmc : maxChild a i = some j) (hleft : 2 * i.val + 1 < sz) :
    compare a[j] a[2 * i.val + 1] |>.isGE := by
  grind only [Std.OrientedOrd.eq_swap, Ordering.swap_lt, Ordering.isGE, Ordering.isLT, maxChild,
  Fin.getElem_fin]

@[grind =]
private theorem maxChild_ge_right [Ord α] [Std.OrientedOrd α] (a : Vector α sz)
    (i j : Fin sz) (hmc : maxChild a i = some j) (hright : 2 * i.val + 2 < sz) :
    compare a[↑j] a[2 * ↑i + 2] |>.isGE := by
  grind only [= Fin.getElem_fin, Std.OrientedOrd.eq_swap, Ordering.swap_lt,
    Ordering.isGE, Ordering.isLT, maxChild]

/-- heapifyDown doesn't modify positions before the starting index. -/
@[grind=]
theorem heapifyDown_preserves_prefix [Ord α] (a : Vector α sz) (i k : Fin sz) (hk : k < ↑i) :
    (heapifyDown a i)[k] = a[k] := by
  induction a, i using heapifyDown.induct <;> grind [heapifyDown]


section heapifyDown

/-- heapifyDown doesn't modify positions outside the starting subtree -/
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
  have hij : i < j := by grind
  have hnsub_j : ¬InSubtree j k := by grind
  rw [heapifyDown_get_of_not_inSubtree hnsub_j]
  grind only [= Fin.getElem_fin, Vector.getElem_swap_of_ne, InSubtree]
termination_by sz - i

theorem heapifyDown_get_of_not_inSubtree' [Ord α] {a : Vector α sz} {i : Fin sz}
    {k : Nat} (hk : k < sz) (hnsub : ¬InSubtree i k) :
    (heapifyDown a i)[k] = a[k] :=
  heapifyDown_get_of_not_inSubtree (k := ⟨k, hk⟩) hnsub

/-- heapifyDown at j preserves WF.children k when i < k < j and j is a child of i -/
theorem heapifyDown_preserves_wf_children_of_lt [Ord α] {a : Vector α sz} {i j k : Fin sz}
    (hchild : j.val = 2 * i.val + 1 ∨ j.val = 2 * i.val + 2)
    (hik : i < k) (hkj : k < j) (hwf : WF.children a k) :
    WF.children (heapifyDown (a.swap ↑i ↑j) ↑j) ↑k := by
  obtain ⟨hwf_left, hwf_right⟩ := hwf
  have hnsub_k : ¬InSubtree j k := InSubtree.not_of_lt (by omega)
  have : (a.swap i j)[k] = a[k] := Vector.getElem_swap_of_ne (by omega) (by omega)
  constructor
  case' left =>  let targetIdx := 2 * k.val + 1
  case' right => let targetIdx := 2 * k.val + 2

  all_goals
    intro hbound
    have : ¬InSubtree j targetIdx := by grind only [InSubtree.not_of_lt]
    rw [heapifyDown_get_of_not_inSubtree hnsub_k,
        heapifyDown_get_of_not_inSubtree' hbound this]
    have : (a.swap i j)[targetIdx] = a[targetIdx]
      := Vector.getElem_swap_of_ne (by omega) (by omega)
    simp_all [targetIdx]



/-- If v dominates all values in the subtree, v dominates the result at root -/
theorem heapifyDown_root_bounded [Ord α] [Std.TransOrd α]
    {a : Vector α sz} {j : Fin sz} {v : α}
    (hge : ∀ k : Fin sz, InSubtree j.val k.val → (compare v a[k]).isGE) :
    (compare v (heapifyDown a j)[j]).isGE := by
  grind only [heapifyDown, InSubtree, Fin.getElem_fin, maxChild_isChild,
    = heapifyDown_preserves_prefix, = Vector.getElem_swap]


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
      . cases Nat.lt_trichotomy j k <;> grind only [heapifyDown_preserves_wf_children_of_lt,
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
    WF (heapifyUp a i) := by
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

theorem mkHeap_wf [Ord α] [Std.TransOrd α] [Std.OrientedOrd α]
    (a : Vector α sz) :
    WF (mkHeap a) := by
  unfold mkHeap
  apply mkHeap.loop_wf
  intro _ _
  constructor
  all_goals
    intro _
    exfalso
    omega


end

end BinaryHeap

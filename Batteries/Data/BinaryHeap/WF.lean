module
public import Batteries.Data.BinaryHeap.Basic

namespace Batteries.BinaryHeap

/-- The size of the underlying vector is preserved when constructing a `BinaryHeap`. -/
theorem vector_size {v : Vector α sz} :
    (BinaryHeap.mk v.toArray).vector.size = sz := by
  simp [Vector.size, Vector.size_toArray, size]

/-- Index `k` lies in the subtree rooted at index `root` in the implicit binary heap tree. -/
@[grind]
inductive InSubtree (root : Nat) : Nat → Prop
  | refl : InSubtree root root
  | left : InSubtree root k → InSubtree root (2 * k + 1)
  | right : InSubtree root k → InSubtree root (2 * k + 2)


namespace InSubtree

theorem le  (ins : InSubtree j k) : j ≤ k := by
  induction ins <;> omega

theorem not_of_lt (hlt : k < j): ¬InSubtree j k := by
  intro hsub
  have := hsub.le
  omega

theorem lt_of_ne (hsub : InSubtree j k) (hne : j ≠ k) : j < k := by grind only [hsub.le]

theorem trans (hij : InSubtree i j) (hjk : InSubtree j k) : InSubtree i k := by
  induction hjk with grind only [InSubtree]

/-- Every index lies in the subtree rooted at 0. -/
theorem zero_root (a : Nat) : InSubtree 0 a := by
  induction a using Nat.strongRecOn with
  | _ n ih =>
    match n with
    | 0 => exact .refl
    | n + 1 =>
      if h : n % 2 = 0 then
        have : n + 1 = 2 * (n / 2) + 1 := by omega
        exact this ▸ .left (ih (n / 2) (by omega))
      else
        have : n + 1 = 2 * (n / 2) + 2 := by omega
        exact this ▸ .right (ih (n / 2) (by omega))
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
public def WF.topDown [Ord α] (v : Vector α sz) : Prop :=
  ∀ i : Fin sz, WF.children v i

/-- The well-formedness property of a binary heap -/
@[expose]
public def WF [Ord α] (self : BinaryHeap α) : Prop :=
  WF.topDown self.vector

namespace WF
variable {α : Type w} {sz : Nat}
/-- All nodes at indices greater than `i` are well-formed (according to WF.children)
    Used when verifying `heapifyDown` -/
def below [Ord α] (a : Vector α sz) (i : Nat) : Prop :=
  ∀ j : Fin sz, i < j.val → WF.children a j

/-- WF.below is monotone: larger threshold means weaker condition. -/
theorem below_mono {a : Vector α sz} {i j : Nat}  [Ord α]
    (hij : i ≤ j) (hbelow : WF.below a i) : WF.below a j := by
  grind only [WF.below]

/-- if i < j, and the heap is well formed below i, then a[i] and a[j] can be swapped
  and the heap will still be well-formed below j --/
theorem below_swap [Ord α] {a : Vector α sz} {i j : Fin sz}
    {hbelow : WF.below a i} {hij : i < j} :
    WF.below (a.swap i j) j := by
  intro k hk_gt_j
  have hk_gt_i : i.val < k.val := Nat.lt_trans ‹_› ‹_›
  obtain ⟨_, _⟩ := hbelow k hk_gt_i
  grind only [= Fin.getElem_fin, = Vector.getElem_swap, WF.children]

/-- Setting a smaller value preserves WF.below -/
theorem set_smaller_wf_below [Ord α] {v : Vector α sz} {i : Fin sz} {x : α}
    (htd : WF.topDown v) :
    WF.below (v.set i x) i := by
  intro j hj
  obtain ⟨hwf_jl, hwf_jr⟩ := htd j
  grind only [Vector.getElem_set, Fin.getElem_fin, WF.children]

/-- For k < i where neither child equals i, set at i preserves WF.children at k -/
theorem set_preserves_wf_children_of_ne [Ord α] {v : Vector α sz} {i k : Fin sz} {x : α}
    (hwf : WF.children v k) (hki : k.val ≠ i.val)
    (hleft_ne : 2 * k.val + 1 ≠ i.val) (hright_ne : 2 * k.val + 2 ≠ i.val) :
    WF.children (v.set i x) k := by
  obtain ⟨hwf_left, hwf_right⟩ := hwf
  grind only [Vector.getElem_set, Fin.getElem_fin, WF.children]

theorem topDown_empty [Ord α] : WF.topDown (#v[] : Vector α 0) := by
  simp [topDown]


theorem topDown_singleton [Ord α] {x : α} : WF.topDown #v[x] := by
  simp [topDown, children]


/-- WF.topDown follows from WF.children at 0 and WF.below at 0 -/
theorem topDown_iff_at_below_zero [Ord α] {a : Vector α sz} {h0 : 0 < sz} :
   WF.children a ⟨0, h0⟩ ∧  WF.below a 0 ↔ WF.topDown a := by
  constructor
  . rintro ⟨_, hbelow⟩
    intro j
    by_cases h : j.val = 0
    . grind only
    . exact hbelow j (by omega)
  . grind only [children, topDown, below]

/-- A node dominates all descendants in its subtree in a well-formed heap. -/
theorem parent_ge_subtree [Ord α] [Std.TransOrd α]
    {a : Vector α sz} {j k : Nat} {hk : k < sz} {hj : j < sz} (hwf_at : WF.children a ⟨j, hj⟩)
    (hwf_below : WF.below a j) (hsub : InSubtree j k) :
    (compare a[j] a[k]).isGE := by
  induction hsub
  case refl => grind only [Ordering.isGE]
  all_goals
    obtain ⟨hwf_m, _⟩ : WF.children a ⟨‹_›, by omega⟩ := by
      grind only [WF.below, InSubtree.not_of_lt]
    grind only [= Fin.getElem_fin, !Std.TransOrd.isGE_trans]

/-- Parent dominates all descendants after setting a smaller value -/
theorem parent_dominates_set_subtree [Ord α] [Std.TransOrd α] [Std.OrientedOrd α]
    {v : Vector α sz} {i : Fin sz} {x : α}
    (htd : WF.topDown v) (h_le : compare x v[i] |>.isLE) (hi : 0 < i.val)
    (m : Fin sz) (hsub : InSubtree i.val m.val) :
    (compare v[(i.val - 1) / 2] (v.set i x)[m]).isGE := by
  let parent : Fin sz := ⟨(i.val - 1) / 2, by omega⟩
  have h_parent_child : i.val = 2 * parent.val + 1 ∨ i.val = 2 * parent.val + 2 := by grind only
  obtain ⟨hwf_parent_l, hwf_parent_r⟩ := htd parent
  have h_parent_ge_i : (compare v[parent] v[i]).isGE := by grind only [= Fin.getElem_fin]
  by_cases hm_eq : m.val = i.val
  · grind only [Std.OrientedOrd.eq_swap, = Fin.getElem_fin, !Std.TransOrd.isGE_trans,
    = Vector.getElem_set, !Ordering.isGE_swap]
  · have : i.val ≠ m.val := by omega
    simp_all only [Fin.getElem_fin, ne_eq, not_false_eq_true, Vector.getElem_set_ne]
    have h_parent_to_i : InSubtree parent.val i.val := by grind only [InSubtree]
    exact WF.parent_ge_subtree
      (hwf_at := htd parent)
      (hwf_below := fun j _ => htd j)
      (hsub := InSubtree.trans h_parent_to_i hsub)

/-- The root element is greater than or equal to all heap elements. -/
theorem root_ge_all [Ord α] [Std.TransOrd α]
    {a : Vector α sz} (hwf : WF.topDown a) (hne : 0 < sz) (k : Fin sz) :
    (compare a[0] a[k]).isGE :=
  parent_ge_subtree
    (hwf_at := hwf ⟨0, hne⟩)
    (hwf_below := fun j _ => hwf j)
    (hsub := InSubtree.zero_root k.val)

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
  · simp_all
  · by_cases hk_child_of_i : (k.val - 1) / 2 = i.val
    · obtain ⟨hleft, hright⟩ := hchildren
      have hk_is_child : k.val = 2 * i.val + 1 ∨ k.val = 2 * i.val + 2 := by omega
      have hk_ne_parent : k.val ≠ (i.val - 1) / 2 := by omega
      rcases hk_is_child with hk_left | hk_right
      · simp_all [show 2 * i.val + 1 < sz by omega]
      · simp_all [show 2 * i.val + 2 < sz by omega]
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
    WF.topDown a ↔ WF.bottomUp a := by
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


theorem topDown_toArray {v : Vector α sz} [Ord α] (h_td : WF.topDown v) : WF ⟨v.toArray⟩ := by
  rintro ⟨ival, _⟩
  obtain ⟨hleft, hright⟩ := h_td ⟨ival, by simp_all [size]⟩
  constructor <;> intro _
  . exact hleft (by grind only [!vector_size])
  . exact hright (by grind only [!vector_size])

/-- Setting a larger value preserves WF.exceptAt -/
theorem exceptAt_set_larger [Ord α] [Std.TransOrd α] [Std.OrientedOrd α]
    {v : Vector α sz} {i : Fin sz} {x : α}
    (hbu : WF.bottomUp v) (h_ge : compare x v[i] |>.isGE) :
    WF.exceptAt (v.set i x) i := by
  intro j hji hj_pos
  by_cases hparent_eq : (j.val - 1) / 2 = i.val
  all_goals
    have hj_parent := hbu j hj_pos
    grind only [Std.OrientedOrd.eq_swap, = Fin.getElem_fin, = Vector.getElem_set,
      !Ordering.isGE_swap, !Std.TransOrd.isLE_trans]

/-- Setting a larger value preserves WF.childLeParent when original heap is well-formed -/
theorem childLeParent_set_larger [Ord α] [Std.TransOrd α] [Std.OrientedOrd α]
    {v : Vector α sz} {i : Fin sz} {x : α}
    (htd : WF.topDown v) (hbu : WF.bottomUp v) (h_ge : compare x v[i] |>.isGE) :
    WF.childLeParent (v.set i x) i := by
  unfold WF.childLeParent
  let parent := (i.val - 1) / 2
  obtain ⟨htd_left, htd_right⟩ := htd i
  constructor
  case' left  => intro hchild; have h_child := htd_left hchild
  case' right => intro hchild; have h_child := htd_right hchild
  all_goals
    by_cases hi : i.val = 0
    · -- i = 0, so parent = 0 = i
      have hset_parent : (v.set i x)[parent] = x := by simp_all [parent]
      grind only [!Std.TransOrd.isLE_trans, Std.OrientedOrd.eq_swap, !Ordering.isGE_swap,
        Vector.getElem_set]
    · -- i ≠ 0, so parent ≠ i
      have h_parent := hbu i (by omega)
      grind only [!Std.TransOrd.isLE_trans, Std.OrientedOrd.eq_swap, !Ordering.isGE_swap,
        WF.parent, Vector.getElem_set]

theorem below_swap_pop [Ord α] {a : Vector α sz} (wf : WF.topDown a)
    (h0 : 0 < sz) :
    WF.below (a.swap 0 (sz - 1)|>.pop) 0 := by
  intro j hj
  constructor
  · intro hleft
    have := (wf ⟨j.val, by omega⟩).1 (by omega : 2 * j.val + 1 < sz)
    grind only [Vector.getElem_swap, Vector.getElem_pop, Fin.getElem_fin]
  · intro hright
    have := (wf ⟨j.val, by omega⟩).2 (by omega : 2 * j.val + 2 < sz)
    grind only [Vector.getElem_swap, Vector.getElem_pop, Fin.getElem_fin]

end WF
end Batteries.BinaryHeap

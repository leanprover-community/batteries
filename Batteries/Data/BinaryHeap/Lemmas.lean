module
import all Batteries.Data.BinaryHeap.Basic
public import Batteries.Data.BinaryHeap.Basic

namespace Batteries.BinaryHeap

theorem vector_size {v : Vector α sz} :
    (BinaryHeap.mk v.toArray).vector.size = sz := by
  simp [Vector.size, Vector.size_toArray, size]


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

@[grind .]
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

/-- Setting a smaller value preserves WF.below -/
theorem set_smaller_wf_below [Ord α] {v : Vector α sz} {i : Fin sz} {x : α}
    (htd : WF.topDown v) :
    WF.below (v.set i x) i := by
  intro j hj
  obtain ⟨hwf_jl, hwf_jr⟩ := htd j
  have h_inej: i.val ≠ j.val := by omega
  constructor
    <;> intro _
    <;> grind only [Vector.getElem_set, Fin.getElem_fin]

/-- For k < i where neither child equals i, set at i preserves WF.children at k -/
theorem set_preserves_wf_children_of_ne [Ord α] {v : Vector α sz} {i k : Fin sz} {x : α}
    (hwf : WF.children v k) (hki : k.val ≠ i.val)
    (hleft_ne : 2 * k.val + 1 ≠ i.val) (hright_ne : 2 * k.val + 2 ≠ i.val) :
    WF.children (v.set i x) k := by
  obtain ⟨hwf_left, hwf_right⟩ := hwf
  constructor <;> intro hbound <;>
    grind only [= Fin.getElem_fin, = Vector.getElem_set]


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


theorem root_ge_subtree [Ord α] [Std.TransOrd α]
    {a : Vector α sz} {j : Nat} (hj : j < sz) {hwf_at : WF.children a ⟨j, hj⟩}
    {hwf_below : WF.below a j} {k : Nat} {hk : k < sz} {hsub : InSubtree j k} :
    (compare a[j] a[k]).isGE := by
  induction hsub
  case refl => grind only [Ordering.isGE]
  all_goals
    obtain ⟨hwf_m, _⟩ : WF.children a ⟨‹_›, by omega⟩ := by grind [WF.below]
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
    exact WF.root_ge_subtree parent.isLt (hwf_at := htd parent)
      (hwf_below := fun j _ => htd j) (hsub := InSubtree.trans h_parent_to_i hsub)


theorem max_ge_all [Ord α] [Std.TransOrd α]
    {a : Vector α sz} (hwf : WF.topDown a) (hne : 0 < sz) (k : Fin sz) :
    (compare a[0] a[k]).isGE :=
  root_ge_subtree hne
    (hwf_at := hwf ⟨0, hne⟩)
    (hwf_below := fun j _ => hwf j)
    (hk := k.isLt)
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


theorem topDown_toArray {v : Vector α sz} [Ord α] (h_td : WF.topDown v) : WF (mk v.toArray) := by
  rintro ⟨ival, _⟩
  obtain ⟨hleft, hright⟩ := h_td ⟨ival, by simp_all [size]⟩
  constructor <;> intro _
  . exact hleft (by grind only [!vector_size])
  . exact hright (by grind only [!vector_size])
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
/-- heapifyDown preserves WF.children at k when k and its children are outside the subtree -/

theorem heapifyDown_preserves_wf_children_of_not_inSubtree [Ord α] {a b : Vector α sz} {i k : Fin sz}
    (hnsub_k : ¬InSubtree i k)
    (hk_eq : a[k] = b[k])
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

theorem swap_pop_wf_below [Ord α] {a : Vector α sz} (wf : WF.topDown a)
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

theorem popMaxVec_wf [Ord α] [Std.TransOrd α] [Std.OrientedOrd α]
    (h : Vector α sz) (wf : WF.topDown h) : WF.topDown (popMaxVec h) := by
  unfold popMaxVec
  simp only
  split
  case isTrue h =>
    subst h
    simp [wf]
  case isFalse hne =>
    split
    case isTrue hnz =>
      have hbelow : WF.below (h.swap 0 (h.size - 1) |>.pop) 0 := by grind only [swap_pop_wf_below wf]
      simp_all [WF.topDown_iff_at_below_zero.mp, heapifyDown_wf (i := ⟨0, by omega⟩) hbelow]
    case isFalse hle =>
      grind only [WF.children, WF.topDown]

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
theorem max_wf [Ord α] [Std.TransOrd α] {self : BinaryHeap α} {hwf : WF self} {h : self.size > 0} :
    ∃ x, self.max = some x ∧ ∀ i : Fin self.size,
    (compare x (self.arr[i.val]'(by simp [size]))).isGE :=
  ⟨self.arr[0], by simp [max], (WF.max_ge_all hwf h ·)⟩

theorem popMax_wf [Ord α] [Std.TransOrd α] [Std.OrientedOrd α]
    {self : BinaryHeap α} {h_wf : WF self} :
    WF (self.popMax) := by
  grind only [popMax, WF, popMaxVec_wf, WF.topDown_toArray]

theorem decreaseKey_wf [Ord α] [Std.TransOrd α] [Std.OrientedOrd α] {self : BinaryHeap α}
    {i : Fin self.size} {x : α} {h_leq : compare x (self.get i) |>.isLE} {h_wf : WF self} :
    WF (self.decreaseKey i x) := by
  unfold decreaseKey

  generalize hv : self.vector = v
  have htd : WF.topDown v := by simp_all [WF]
  have h_leq' : compare x v[i] |>.isLE := by
    have : self.size = self.arr.size := by simp [size]
    simp_all [get, ← hv, vector]

  suffices WF.topDown (heapifyDown (v.set i x) i) by
    exact WF.topDown_toArray this

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

end BinaryHeap

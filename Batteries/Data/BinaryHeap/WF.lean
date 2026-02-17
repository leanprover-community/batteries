/-
Copyright (c) 2026 Chad Sharp. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chad Sharp
-/
module
public import Batteries.Data.BinaryHeap.Basic
import all Batteries.Data.BinaryHeap.Basic

namespace Batteries.BinaryHeap

public section

/-- The primary local correctness property for the heap. A node should be >= both its children
    (if it has them).
-/
@[expose]
def WF.Children [Ord α] (a : Vector α sz) (i : Fin sz) : Prop :=
  let left := 2 * i.val + 1
  let right := left + 1
  (∀ _ : left < sz, compare a[i] a[left] |>.isGE) ∧
  (∀ _ : right < sz, compare a[i] a[right] |>.isGE)

/-- The vector underlying a `BinaryHeap` is well-formed iff every node is ≥ any children it has -/
@[expose]
def WF.TopDown [Ord α] (v : Vector α sz) : Prop :=
  ∀ i : Fin sz, WF.Children v i

/-- The well-formedness property of a binary heap -/
@[expose]
def WF [Ord α] (heap : BinaryHeap α) : Prop :=
  WF.TopDown heap.vector

end

def WF.toTopDown [Ord α] {heap : BinaryHeap α} (hwf : WF heap) : WF.TopDown heap.vector := by
  simp_all [WF]

/-- `WF.children` depends only on the values at position `k` and its two children.
    If those values agree between two vectors, `WF.children` transfers. -/
theorem WF.Children.congr [Ord α] {a b : Vector α sz} {k : Fin sz}
    (hwf : WF.Children a k)
    (hk : b[k] = a[k])
    (hl : ∀ _ : 2 * k.val + 1 < sz, b[2 * k.val + 1] = a[2 * k.val + 1])
    (hr : ∀ _ : 2 * k.val + 2 < sz, b[2 * k.val + 2] = a[2 * k.val + 2]) :
    WF.Children b k := by
  simp_all [WF.Children]

/-- Index `k` lies in the subtree rooted at index `root` in the implicit binary heap tree. -/
@[grind]
inductive InSubtree (root : Nat) : Nat → Prop
  | refl : InSubtree root root
  | left : InSubtree root k → InSubtree root (2 * k + 1)
  | right : InSubtree root k → InSubtree root (2 * k + 2)

namespace InSubtree

@[simp]
theorem le (ins : InSubtree j k) : j ≤ k := by
  induction ins with omega

theorem not_of_lt (hlt : k < j) : ¬InSubtree j k := by
  intro hsub
  have := hsub.le
  omega

theorem lt_of_ne (hsub : InSubtree j k) (hne : j ≠ k) : j < k := by grind only [hsub.le]

theorem trans (hij : InSubtree i j) (hjk : InSubtree j k) : InSubtree i k := by
  induction hjk with grind only [InSubtree]

theorem ne_of_lt (h: i < j) (hins : InSubtree j k) : k ≠ i := by
  have : j ≤ k := InSubtree.le hins
  omega

/-- Every index is a member of the subtree rooted at 0. -/
theorem mem_of_zero (a : Nat) : InSubtree 0 a := by
  induction a using Nat.strongRecOn with | _ n ih =>
  match n with
  | 0 => exact .refl
  | n + 1 =>
    if h : n % 2 = 0 then
      have : n + 1 = 2 * (n / 2) + 1 := by omega
      exact this ▸ .left (ih (n / 2) (by omega))
    else
      have : n + 1 = 2 * (n / 2) + 2 := by omega
      exact this ▸ .right (ih (n / 2) (by omega))

/-- A child index is in the subtree of its parent. -/
theorem of_child (h : j = 2 * i + 1 ∨ j = 2 * i + 2) : InSubtree i j := by
  rcases h with h | h <;> (subst h; constructor; exact .refl)

end InSubtree

namespace WF
/-- All nodes at indices greater than `i` are well-formed (according to WF.children)
    Used when verifying `heapifyDown` -/
def Below [Ord α] (a : Vector α sz) (i : Nat) : Prop :=
  ∀ j : Fin sz, i < j.val → WF.Children a j

/-- WF.Below is monotone: larger threshold means weaker condition. -/
theorem Below.of_le {a : Vector α sz} [Ord α]
    (hij : i ≤ j) (hbelow : WF.Below a i) : WF.Below a j := by
  grind only [WF.Below]

/-- if i < j, and the heap is well formed below i, then a[i] and a[j] can be swapped
  and the heap will still be well-formed below j --/
theorem Below.swap [Ord α] {a : Vector α sz} {i j : Fin sz} (hbelow : WF.Below a i) (hij : i
  < j) :
    WF.Below (a.swap i j i.isLt j.isLt) j := by
  intro k hk_gt_j
  apply WF.Children.congr (hbelow k (Nat.lt_trans hij hk_gt_j))
    <;> intros <;> apply Vector.getElem_swap_of_ne <;> omega

/-- For k ≠ i where neither child of k equals i, set at i preserves WF.children at k -/
theorem Children.set_of_ne [Ord α] {v : Vector α sz} {i k : Fin sz}
    (hwf : WF.Children v k) (hki : k.val ≠ i.val)
    (hleft_ne : i.val ≠ 2 * k.val + 1) (hright_ne : i.val ≠ 2 * k.val + 2) :
    WF.Children (v.set i x i.isLt) k := by
  apply WF.Children.congr hwf <;> intros <;> apply Vector.getElem_set_ne <;> omega

/-- Setting a child to a smaller value preserves WF.Children at the parent -/
theorem Children.set_of_ge_child [Ord α] [Std.TransOrd α] {v : Vector α sz} {k i : Fin sz}
    (hwf : WF.Children v k) (h_child : i.val = 2 * k.val + 1 ∨ i.val = 2 * k.val + 2)
    (h_ge : compare v[k] x |>.isGE) :
    WF.Children (v.set i x i.isLt) k := by
  have hki : k.val ≠ i.val := by omega
  have ⟨hwf_l, hwf_r⟩ := hwf
  cases h_child <;> grind only [WF.Children, = Fin.getElem_fin, = Vector.getElem_set]

/-- Setting a smaller value preserves WF.Below -/
theorem Below.of_topDown_set [Ord α] {v : Vector α sz} {i : Fin sz} (htd : WF.TopDown v) :
    WF.Below (v.set i x i.isLt) i := by
  intro j hj
  apply (htd j).set_of_ne <;> omega

/-- An empty vector is trivially well-formed (no nodes to violate the heap property). -/
@[simp]
theorem TopDown.empty [Ord α] : WF.TopDown (#v[] : Vector α 0) := by
  simp [WF.TopDown]

/-- A single-element vector is trivially well-formed (no children to compare with). -/
@[simp]
theorem TopDown.singleton [Ord α] {x : α} : WF.TopDown #v[x] := by
  simp [WF.TopDown, WF.Children]

/-- WF.topDown follows from WF.children at 0 and WF.Below at 0 -/
theorem TopDown.iff_root_and_below [Ord α] {a : Vector α sz} {h0 : 0 < sz} :
   WF.Children a ⟨0, h0⟩ ∧  WF.Below a 0 ↔ WF.TopDown a := by
  grind only [WF.Children, WF.TopDown, WF.Below]

theorem TopDown.children_and_below [Ord α] {a : Vector α sz} (htd : WF.TopDown a) (i : Fin sz) :
    WF.Children a i ∧ WF.Below a i :=
  ⟨htd i, fun j _ => htd j⟩

/-- A node dominates all descendants in its subtree in a well-formed heap. -/
theorem parent_ge_subtree [Ord α] [Std.TransOrd α]
    {a : Vector α sz} {hk : k < sz} {hj : j < sz} (hwf_at : WF.Children a ⟨j, hj⟩)
    (hwf_below : WF.Below a j) (hsub : InSubtree j k) :
    (compare a[j] a[k]).isGE := by
  induction hsub
  case refl => grind only [Ordering.isGE]
  all_goals
    have ⟨hwf_m, _⟩ : WF.Children a ⟨‹_›, by omega⟩ := by
      grind only [WF.Below, InSubtree.not_of_lt]
    grind only [= Fin.getElem_fin, !Std.TransOrd.isGE_trans]

/-- If v dominates the new value at j, v dominated the original value at j,
    the original array was well-formed at and below j, and b agrees with a outside position j,
    then v dominates everything in b's subtree at j. -/
theorem ge_subtree_of_modify [Ord α] [Std.TransOrd α]
    {a b : Vector α sz} {j : Fin sz} {v : α}
    (hge : compare v a[j] |>.isGE)
    (hwf_at : WF.Children a j)
    (hwf_below : WF.Below a j)
    (hge_new : compare v b[j] |>.isGE)
    (hunchanged : ∀ k : Fin sz, InSubtree j.val k.val → j.val ≠ k.val → b[k] = a[k]) :
    ∀ m : Fin sz, InSubtree j.val m.val → (compare v b[m]).isGE := by
  intro m hsub
  by_cases hm_eq : m.val = j.val
  · simp_all
  · rw [hunchanged m hsub (Ne.symm hm_eq)]
    apply Std.TransOrd.isGE_trans hge
    exact parent_ge_subtree hwf_at hwf_below hsub

/-- Parent dominates all descendants after setting a smaller value -/
theorem TopDown.parent_ge_subtree_of_set [Ord α] [Std.TransOrd α] {v : Vector α sz} {i : Fin sz}
    (htd : WF.TopDown v) (h_le : compare v[i] x |>.isGE) (hi : 0 < i.val)
    (m : Fin sz) (hsub : InSubtree i.val m.val) :
    (compare v[(i.val - 1) / 2] (v.set i x i.isLt)[m]).isGE := by
  let parent : Fin sz := ⟨(i.val - 1) / 2, by omega⟩
  have h_parent_ge_i : (compare v[parent] v[i]).isGE := by
    have ⟨_, _⟩ := htd parent
    grind only [= Fin.getElem_fin]
  have ⟨h_child, h_below⟩ := htd.children_and_below i
  apply ge_subtree_of_modify h_parent_ge_i h_child h_below
  . simp only [Fin.getElem_fin, Vector.getElem_set_self]
    exact Std.TransOrd.isGE_trans h_parent_ge_i h_le
  . intros
    exact Vector.getElem_set_ne _ _ ‹_›
  . exact hsub

/-- a[j] dominates everything in (a.swap i j)'s subtree at j when i < j and a[i] < a[j] -/
theorem swap_preserves_ge_subtree [Ord α] [Std.TransOrd α]
    {a : Vector α sz} {i j k : Fin sz} (h_ij : i < j) (h_ge : (compare a[j] a[i]).isGE)
    (hbelow : WF.Below a i) (hsub : InSubtree j k) :
    (compare a[j] (a.swap i j i.isLt j.isLt)[k]).isGE := by
  have hge : (compare a[j] a[j]).isGE := by grind only [Ordering.isGE]
  have hwf_at := hbelow j h_ij
  have hwf_below := hbelow.of_le (Fin.le_of_lt h_ij)
  apply ge_subtree_of_modify hge hwf_at hwf_below
  · simp_all
  · intro m hsub hne
    exact Vector.getElem_swap_of_ne (InSubtree.ne_of_lt h_ij hsub) (Ne.symm hne)
  · exact hsub

/-- The root element is greater than or equal to all heap elements. -/
theorem TopDown.root_ge_all [Ord α] [Std.TransOrd α]
    {a : Vector α sz} (hwf : WF.TopDown a) (hne : 0 < sz) (k : Fin sz) :
    (compare a[0] a[k]).isGE :=
  have ⟨hwf_at, hwf_below⟩ := hwf.children_and_below ⟨0, hne⟩
  parent_ge_subtree hwf_at hwf_below (InSubtree.mem_of_zero k.val)

/-- "Dual" correctness property to WF.children. A parent should be >= current node.
    Used when verifying heapifyUp -/
def Parent [Ord α] (a : Vector α sz) (i : Fin sz) : Prop :=
  ∀ _ : 0 < i.val, compare a[(i.val - 1)/2] a[i] |>.isGE

/-- The parent of node `i` is >= node `i`'s chilren
    Part of the invariant required/maintained by heapifyUp
-/
def ParentGeChildren [Ord α] (a: Vector α sz) (i : Fin sz) : Prop :=
  let parent := (i.val - 1) / 2
  let left := 2 * i.val + 1
  let right := left + 1
  (∀ _ : left < sz, compare a[parent] a[left] |>.isGE) ∧
  (∀ _ : right < sz, compare a[parent] a[right] |>.isGE)

/-- Every other node (except possibly i) is <= its parent (if it has one)
    Part of the invariant required/maintained by heapifyUp
-/
def ExceptAt [Ord α] (a : Vector α sz) (i : Fin sz) : Prop :=
  ∀ j : Fin sz, i ≠ j → Parent a j

/-- If exceptAt i and parentGeChildren i, swap preserves exceptAt at parent -/
theorem ExceptAt.swap_parent [Ord α] [Std.TransOrd α]
    {a : Vector α sz} {i : Fin sz}
    (h_ge : compare a[i] a[(i.val - 1) / 2] |>.isGE)
    (hexcept : ExceptAt a i)
    (hchildren : ParentGeChildren a i) :
    ExceptAt (a.swap i ((i.val - 1) / 2) i.isLt (by omega)) ⟨(i.val - 1) / 2, by omega⟩ := by
  intro k hkj hk_pos
  by_cases hki : k.val = i.val
  · simp_all
  · by_cases hk_child_of_i : (k.val - 1) / 2 = i.val
    · have ⟨hleft, hright⟩ := hchildren
      have hk_is_child : k.val = 2 * i.val + 1 ∨ k.val = 2 * i.val + 2 := by omega
      have hk_ne_parent : k.val ≠ (i.val - 1) / 2 := by omega
      rcases hk_is_child with hk_left | hk_right <;> simp_all
    · unfold ExceptAt Parent at *
      grind only [= Fin.getElem_fin, = Vector.getElem_swap, !Std.TransOrd.isGE_trans]

/-- If exceptAt a i, swap preserves parentGeChildren at parent -/
theorem ParentGeChildren.swap_parent [Ord α] [Std.TransOrd α]
    {a : Vector α sz} {i : Fin sz}
    (h_ge : compare a[i] a[(i.val - 1)/2] |>.isGE)
    (hexcept : ExceptAt a i) :
    ParentGeChildren
      (a.swap i ((i.val - 1) / 2) i.isLt (by omega)) ⟨(i.val - 1) / 2, by omega⟩ := by
  let j := (i.val - 1) / 2
  constructor
  case' left  => let targetIdx := 2 * j + 1
  case' right => let targetIdx := 2 * j + 2
  all_goals
    intro hside
    unfold ExceptAt Parent at hexcept
    by_cases hli : i.val = targetIdx
    · have hji : j ≠ i.val := by omega
      grind only [= Fin.getElem_fin, = Vector.getElem_swap]
    · have hparent_eq : (targetIdx - 1) / 2 = j := by omega
      have h1 := hexcept ⟨targetIdx, hside⟩ (by grind only) (by grind only)
      by_cases hj_pos : 0 < j <;>
        grind only [= Fin.getElem_fin, = Vector.getElem_swap, !Std.TransOrd.isGE_trans]

/- Dual global correctness property to `WF`. The vector underlying a BinaryHeap is well-formed
  iff all nodes are ≤ their parent.
  Used when verifying heapifyUp.
-/
def BottomUp [Ord α] (v : Vector α sz) : Prop :=
  ∀ i : Fin sz, Parent v i

/- WF and WF.BottomUp are equivalent -/
theorem TopDown.iff_bottomUp [Ord α] [Std.OrientedOrd α] {a : Vector α sz} :
    WF.TopDown a ↔ WF.BottomUp a := by
  constructor
  · intro htd i
    have := htd ⟨(i.val - 1) / 2, by omega⟩
    grind only [WF.Children, Parent, = Fin.getElem_fin]
  · intro hbu i
    constructor <;> intro hchild
    case' mpr.left => have := hbu ⟨2 * i.val + 1, hchild⟩
    case' mpr.right => have := hbu ⟨2 * i.val + 2, hchild⟩
    all_goals grind only [Parent, = Fin.getElem_fin]

/-- If exception is at 0, then bottomUp holds -/
theorem BottomUp.of_exceptAt_root [Ord α] {a : Vector α sz} (h : 0 < sz)
    (hexcept : ExceptAt a ⟨0, h⟩) :
    WF.BottomUp a := by
  grind only [Parent, Fin.ext_iff, WF.BottomUp, ExceptAt]

/-- If both the parent property and exceptAt property hold at i, then the heap is bottomUp. -/
theorem BottomUp.of_parent_and_exceptAt [Ord α] {a : Vector α sz} {i : Fin sz}
    (hexcept : ExceptAt a i) (hparent : Parent a i) :
    WF.BottomUp a := by
  grind only [BottomUp, Parent, ExceptAt]

/-- A well-formed vector transfers its well-formedness to a BinaryHeap created from its array
  representation. -/
theorem of_topDown {v : Vector α sz} [Ord α] (h_td : WF.TopDown v) : WF ⟨v.toArray⟩ := by
  intro ⟨ival, _⟩
  have ⟨hleft, hright⟩ := h_td ⟨ival, by simp_all [size]⟩
  constructor
    <;> intros
    <;> (first | apply hleft | apply hright)
    <;> simp_all [Vector.size_toArray, BinaryHeap.size]

/-- Setting a larger value preserves WF.exceptAt -/
theorem ExceptAt.set_of_ge [Ord α] [Std.TransOrd α]
    {v : Vector α sz} {i : Fin sz} {x : α}
    (hbu : WF.BottomUp v) (h_ge : compare x v[i] |>.isGE) :
    ExceptAt (v.set i x i.isLt) i := by
  intro j hji hj_pos
  by_cases hparent_eq : (j.val - 1) / 2 = i.val
  all_goals
    have hj_parent := hbu j hj_pos
    grind only [= Fin.getElem_fin, = Vector.getElem_set, !Std.TransOrd.isGE_trans]

/-- Setting a larger value preserves WF.parentGeChildren when original heap is well-formed -/
theorem ParentGeChildren.set_of_ge [Ord α] [Std.TransOrd α]
    {v : Vector α sz} {i : Fin sz} (hbu : WF.BottomUp v) (h_ge : compare x v[i] |>.isGE) :
    ParentGeChildren (v.set i x i.isLt) i := by
  let parent := (i.val - 1) / 2
  have htd : WF.TopDown v := by rwa [← WF.TopDown.iff_bottomUp] at hbu
  have ⟨htd_left, htd_right⟩ := htd i
  constructor <;> intro hchild
  case' left  => have := htd_left hchild
  case' right => have := htd_right hchild
  all_goals
    by_cases hi : i.val = 0
    · have hset_parent : (v.set i x i.isLt)[parent] = x := by simp_all [parent]
      grind only [!Std.TransOrd.isGE_trans, Vector.getElem_set_ne]
    · have h_parent := hbu i (by omega)
      grind only [!Std.TransOrd.isGE_trans, Parent, Vector.getElem_set_ne]

/-- Swapping the root with the last element and then popping maintains the Below invariant at the
  root for heapifyDown. -/
theorem Below.of_topDown_swap_pop [Ord α] {a : Vector α sz} (hwf : WF.TopDown a) (h0 : 0 < sz) :
    WF.Below (a.swap 0 (sz - 1) h0 (by omega) |>.pop) 0 := by
  intro j _
  have ⟨hwf_l, hwf_r⟩ := hwf ⟨j.val, by omega⟩
  constructor <;> intro
  case' left  => have := hwf_l (show 2 * j.val + 1 < sz by omega)
  case' right => have := hwf_r (show 2 * j.val + 2 < sz by omega)
  all_goals grind only [Vector.getElem_swap, Vector.getElem_pop, Fin.getElem_fin]

/-- Prove WF.Children for all k ≥ lo by splitting at pivot i:
    k > i from hbelow, k = i from hchildren, k ∈ [lo, i) from hrange -/
theorem children_of_split [Ord α] {a : Vector α sz} {lo : Nat} {i : Fin sz}
    (hchildren_i : WF.Children a i)
    (hbelow_i : WF.Below a i)
    (hrange : ∀ k : Fin sz, lo ≤ k.val → k.val < i.val → WF.Children a k) :
    ∀ {k : Fin sz}, lo ≤ k.val → WF.Children a k := by
  intro k hlo
  rcases Nat.lt_trichotomy i.val k.val with hik | heq | hki
  · exact hbelow_i k hik
  · exact Fin.ext heq ▸ hchildren_i
  · exact hrange k hlo hki

/-- Build WF.TopDown from WF.Children at i, WF.Below at i, and a proof for positions < i -/
theorem TopDown.of_children_below_and_above [Ord α] {a : Vector α sz} {i : Fin sz}
    (hchildren_i : WF.Children a i)
    (hbelow_i : WF.Below a i)
    (habove : ∀ k : Fin sz, k.val < i.val → WF.Children a k) :
    WF.TopDown a := by
  intro
  apply children_of_split hchildren_i hbelow_i
  . intro k _ hki
    exact habove k hki
  . exact Nat.zero_le _

/-- Build WF.Below at i from WF.Children at j, WF.Below at j, and a proof for positions between -/
theorem Below.of_children_below_and_between [Ord α] {a : Vector α sz} {i j : Fin sz}
    (hchildren_j : WF.Children a j)
    (hbelow_j : WF.Below a j)
    (hbetween : ∀ k : Fin sz, i.val < k.val → k.val < j.val → WF.Children a k) :
    WF.Below a i := by
  grind only [Below, children_of_split]

end WF
end Batteries.BinaryHeap

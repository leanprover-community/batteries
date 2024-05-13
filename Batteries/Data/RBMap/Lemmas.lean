/-
Copyright (c) 2022 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Batteries.Data.RBMap.Alter
import Batteries.Data.List.Lemmas

/-!
# Additional lemmas for Red-black trees
-/

namespace Batteries
namespace RBNode
open RBColor

attribute [simp] fold foldl foldr Any forM foldlM Ordered

section depth

/--
`O(n)`. `depth t` is the maximum number of nodes on any path to a leaf.
It is an upper bound on most tree operations.
-/
def depth : RBNode α → Nat
  | nil => 0
  | node _ a _ b => max a.depth b.depth + 1

theorem size_lt_depth : ∀ t : RBNode α, t.size < 2 ^ t.depth
  | .nil => (by decide : 0 < 1)
  | .node _ a _ b => by
    rw [size, depth, Nat.add_right_comm, Nat.pow_succ, Nat.mul_two]
    refine Nat.add_le_add
      (Nat.lt_of_lt_of_le a.size_lt_depth ?_) (Nat.lt_of_lt_of_le b.size_lt_depth ?_)
    · exact Nat.pow_le_pow_of_le_right (by decide) (Nat.le_max_left ..)
    · exact Nat.pow_le_pow_of_le_right (by decide) (Nat.le_max_right ..)

/--
`depthLB c n` is the best upper bound on the depth of any balanced red-black tree
with root colored `c` and black-height `n`.
-/
def depthLB : RBColor → Nat → Nat
  | red, n => n + 1
  | black, n => n

theorem depthLB_le : ∀ c n, n ≤ depthLB c n
  | red, _ => Nat.le_succ _
  | black, _ => Nat.le_refl _

/--
`depthUB c n` is the best upper bound on the depth of any balanced red-black tree
with root colored `c` and black-height `n`.
-/
def depthUB : RBColor → Nat → Nat
  | red, n => 2 * n + 1
  | black, n => 2 * n

theorem depthUB_le : ∀ c n, depthUB c n ≤ 2 * n + 1
  | red, _ => Nat.le_refl _
  | black, _ => Nat.le_succ _

theorem depthUB_le_two_depthLB : ∀ c n, depthUB c n ≤ 2 * depthLB c n
  | red, _ => Nat.le_succ _
  | black, _ => Nat.le_refl _

theorem Balanced.depth_le : @Balanced α t c n → t.depth ≤ depthUB c n
  | .nil => Nat.le_refl _
  | .red hl hr => Nat.succ_le_succ <| Nat.max_le.2 ⟨hl.depth_le, hr.depth_le⟩
  | .black hl hr => Nat.succ_le_succ <| Nat.max_le.2
    ⟨Nat.le_trans hl.depth_le (depthUB_le ..), Nat.le_trans hr.depth_le (depthUB_le ..)⟩

theorem Balanced.le_size : @Balanced α t c n → 2 ^ depthLB c n ≤ t.size + 1
  | .nil => Nat.le_refl _
  | .red hl hr => by
    rw [size, Nat.add_right_comm (size _), Nat.add_assoc, depthLB, Nat.pow_succ, Nat.mul_two]
    exact Nat.add_le_add hl.le_size hr.le_size
  | .black hl hr => by
    rw [size, Nat.add_right_comm (size _), Nat.add_assoc, depthLB, Nat.pow_succ, Nat.mul_two]
    refine Nat.add_le_add (Nat.le_trans ?_ hl.le_size) (Nat.le_trans ?_ hr.le_size) <;>
      exact Nat.pow_le_pow_of_le_right (by decide) (depthLB_le ..)

theorem Balanced.depth_bound (h : @Balanced α t c n) : t.depth ≤ 2 * (t.size + 1).log2 :=
  Nat.le_trans h.depth_le <| Nat.le_trans (depthUB_le_two_depthLB ..) <|
    Nat.mul_le_mul_left _ <| (Nat.le_log2 (Nat.succ_ne_zero _)).2 h.le_size

/--
A well formed tree has `t.depth ∈ O(log t.size)`, that is, it is well balanced.
This justifies the `O(log n)` bounds on most searching operations of `RBSet`.
-/
theorem WF.depth_bound {t : RBNode α} (h : t.WF cmp) : t.depth ≤ 2 * (t.size + 1).log2 :=
  let ⟨_, _, h⟩ := h.out.2; h.depth_bound

end depth

@[simp] theorem min?_reverse (t : RBNode α) : t.reverse.min? = t.max? := by
  unfold RBNode.max?; split <;> simp [RBNode.min?]
  unfold RBNode.min?; rw [min?.match_1.eq_3]
  · apply min?_reverse
  · simpa [reverse_eq_iff]

@[simp] theorem max?_reverse (t : RBNode α) : t.reverse.max? = t.min? := by
  rw [← min?_reverse, reverse_reverse]

@[simp] theorem mem_nil {x} : ¬x ∈ (.nil : RBNode α) := by simp [(·∈·), EMem]
@[simp] theorem mem_node {y c a x b} :
    y ∈ (.node c a x b : RBNode α) ↔ y = x ∨ y ∈ a ∨ y ∈ b := by simp [(·∈·), EMem]

theorem All_def {t : RBNode α} : t.All p ↔ ∀ x ∈ t, p x := by
  induction t <;> simp [or_imp, forall_and, *]

theorem Any_def {t : RBNode α} : t.Any p ↔ ∃ x ∈ t, p x := by
  induction t <;> simp [or_and_right, exists_or, *]

theorem memP_def : MemP cut t ↔ ∃ x ∈ t, cut x = .eq := Any_def

theorem mem_def : Mem cmp x t ↔ ∃ y ∈ t, cmp x y = .eq := Any_def

theorem mem_congr [@TransCmp α cmp] {t : RBNode α} (h : cmp x y = .eq) :
    Mem cmp x t ↔ Mem cmp y t := by simp [Mem, TransCmp.cmp_congr_left' h]

theorem isOrdered_iff' [@TransCmp α cmp] {t : RBNode α} :
    isOrdered cmp t L R ↔
    (∀ a ∈ L, t.All (cmpLT cmp a ·)) ∧
    (∀ a ∈ R, t.All (cmpLT cmp · a)) ∧
    (∀ a ∈ L, ∀ b ∈ R, cmpLT cmp a b) ∧
    Ordered cmp t := by
  induction t generalizing L R with
  | nil =>
    simp [isOrdered]; split <;> simp [cmpLT_iff]
    next h => intro _ ha _ hb; cases h _ _ ha hb
  | node _ l v r =>
    simp [isOrdered, *]
    exact ⟨
      fun ⟨⟨Ll, lv, Lv, ol⟩, ⟨vr, rR, vR, or⟩⟩ => ⟨
        fun _ h => ⟨Lv _ h, Ll _ h, (Lv _ h).trans_l vr⟩,
        fun _ h => ⟨vR _ h, (vR _ h).trans_r lv, rR _ h⟩,
        fun _ hL _ hR => (Lv _ hL).trans (vR _ hR),
        lv, vr, ol, or⟩,
      fun ⟨hL, hR, _, lv, vr, ol, or⟩ => ⟨
        ⟨fun _ h => (hL _ h).2.1, lv, fun _ h => (hL _ h).1, ol⟩,
        ⟨vr, fun _ h => (hR _ h).2.2, fun _ h => (hR _ h).1, or⟩⟩⟩

theorem isOrdered_iff [@TransCmp α cmp] {t : RBNode α} :
    isOrdered cmp t ↔ Ordered cmp t := by simp [isOrdered_iff']

instance (cmp) [@TransCmp α cmp] (t) : Decidable (Ordered cmp t) := decidable_of_iff _ isOrdered_iff

/--
A cut is like a homomorphism of orderings: it is a monotonic predicate with respect to `cmp`,
but it can make things that are distinguished by `cmp` equal.
This is sufficient for `find?` to locate an element on which `cut` returns `.eq`,
but there may be other elements, not returned by `find?`, on which `cut` also returns `.eq`.
-/
class IsCut (cmp : α → α → Ordering) (cut : α → Ordering) : Prop where
  /-- The set `{x | cut x = .lt}` is downward-closed. -/
  le_lt_trans [TransCmp cmp] : cmp x y ≠ .gt → cut x = .lt → cut y = .lt
  /-- The set `{x | cut x = .gt}` is upward-closed. -/
  le_gt_trans [TransCmp cmp] : cmp x y ≠ .gt → cut y = .gt → cut x = .gt

theorem IsCut.lt_trans [IsCut cmp cut] [TransCmp cmp]
    (H : cmp x y = .lt) : cut x = .lt → cut y = .lt :=
  IsCut.le_lt_trans <| TransCmp.gt_asymm <| OrientedCmp.cmp_eq_gt.2 H

theorem IsCut.gt_trans [IsCut cmp cut] [TransCmp cmp]
    (H : cmp x y = .lt) : cut y = .gt → cut x = .gt :=
  IsCut.le_gt_trans <| TransCmp.gt_asymm <| OrientedCmp.cmp_eq_gt.2 H

theorem IsCut.congr [IsCut cmp cut] [TransCmp cmp] (H : cmp x y = .eq) : cut x = cut y := by
  cases ey : cut y
  · exact IsCut.le_lt_trans (fun h => nomatch H.symm.trans <| OrientedCmp.cmp_eq_gt.1 h) ey
  · cases ex : cut x
    · exact IsCut.le_lt_trans (fun h => nomatch H.symm.trans h) ex |>.symm.trans ey
    · rfl
    · refine IsCut.le_gt_trans (cmp := cmp) (fun h => ?_) ex |>.symm.trans ey
      cases H.symm.trans <| OrientedCmp.cmp_eq_gt.1 h
  · exact IsCut.le_gt_trans (fun h => nomatch H.symm.trans h) ey

/--
`IsStrictCut` upgrades the `IsCut` property to ensure that at most one element of the tree
can match the cut, and hence `find?` will return the unique such element if one exists.
-/
class IsStrictCut (cmp : α → α → Ordering) (cut : α → Ordering) extends IsCut cmp cut : Prop where
  /-- If `cut = x`, then `cut` and `x` have compare the same with respect to other elements. -/
  exact [TransCmp cmp] : cut x = .eq → cmp x y = cut y

/-- A "representable cut" is one generated by `cmp a` for some `a`. This is always a valid cut. -/
instance (cmp) (a : α) : IsStrictCut cmp (cmp a) where
  le_lt_trans h₁ h₂ := TransCmp.lt_le_trans h₂ h₁
  le_gt_trans h₁ := Decidable.not_imp_not.1 (TransCmp.le_trans · h₁)
  exact h := (TransCmp.cmp_congr_left h).symm

section find?

theorem find?_some_eq_eq {t : RBNode α} : x ∈ t.find? cut → cut x = .eq := by
  induction t <;> simp [find?]; split <;> try assumption
  intro | rfl => assumption

theorem find?_some_mem {t : RBNode α} : x ∈ t.find? cut → x ∈ t := by
  induction t <;> simp [find?]; split <;> simp (config := {contextual := true}) [*]

theorem find?_some_memP {t : RBNode α} (h : x ∈ t.find? cut) : MemP cut t :=
  memP_def.2 ⟨_, find?_some_mem h, find?_some_eq_eq h⟩

theorem Ordered.memP_iff_find? [@TransCmp α cmp] [IsCut cmp cut] (ht : Ordered cmp t) :
    MemP cut t ↔ ∃ x, t.find? cut = some x := by
  refine ⟨fun H => ?_, fun ⟨x, h⟩ => find?_some_memP h⟩
  induction t with simp [find?] at H ⊢
  | nil => cases H
  | node _ l _ r ihl ihr =>
    let ⟨lx, xr, hl, hr⟩ := ht
    split
    · next ev =>
      refine ihl hl ?_
      rcases H with ev' | hx | hx
      · cases ev.symm.trans ev'
      · exact hx
      · have ⟨z, hz, ez⟩ := Any_def.1 hx
        cases ez.symm.trans <| IsCut.lt_trans (All_def.1 xr _ hz).1 ev
    · next ev =>
      refine ihr hr ?_
      rcases H with ev' | hx | hx
      · cases ev.symm.trans ev'
      · have ⟨z, hz, ez⟩ := Any_def.1 hx
        cases ez.symm.trans <| IsCut.gt_trans (All_def.1 lx _ hz).1 ev
      · exact hx
    · exact ⟨_, rfl⟩

theorem Ordered.unique [@TransCmp α cmp] (ht : Ordered cmp t)
    (hx : x ∈ t) (hy : y ∈ t) (e : cmp x y = .eq) : x = y := by
  induction t with
  | nil => cases hx
  | node _ l _ r ihl ihr =>
    let ⟨lx, xr, hl, hr⟩ := ht
    rcases hx, hy with ⟨rfl | hx | hx, rfl | hy | hy⟩
    · rfl
    · cases e.symm.trans <| OrientedCmp.cmp_eq_gt.2 (All_def.1 lx _ hy).1
    · cases e.symm.trans (All_def.1 xr _ hy).1
    · cases e.symm.trans (All_def.1 lx _ hx).1
    · exact ihl hl hx hy
    · cases e.symm.trans ((All_def.1 lx _ hx).trans (All_def.1 xr _ hy)).1
    · cases e.symm.trans <| OrientedCmp.cmp_eq_gt.2 (All_def.1 xr _ hx).1
    · cases e.symm.trans <| OrientedCmp.cmp_eq_gt.2
        ((All_def.1 lx _ hy).trans (All_def.1 xr _ hx)).1
    · exact ihr hr hx hy

theorem Ordered.find?_some [@TransCmp α cmp] [IsStrictCut cmp cut] (ht : Ordered cmp t) :
    t.find? cut = some x ↔ x ∈ t ∧ cut x = .eq := by
  refine ⟨fun h => ⟨find?_some_mem h, find?_some_eq_eq h⟩, fun ⟨hx, e⟩ => ?_⟩
  have ⟨y, hy⟩ := ht.memP_iff_find?.1 (memP_def.2 ⟨_, hx, e⟩)
  exact ht.unique hx (find?_some_mem hy) ((IsStrictCut.exact e).trans (find?_some_eq_eq hy)) ▸ hy

end find?

section lowerBound?

/-- The value `x` returned by `lowerBound?` is less or equal to the `cut`. -/
theorem lowerBound?_le' {t : RBNode α} (H : ∀ {x}, x ∈ lb → cut x ≠ .lt) :
    t.lowerBound? cut lb = some x → cut x ≠ .lt := by
  induction t generalizing lb with
  | nil => exact H
  | node _ _ _ _ ihl ihr =>
    simp [lowerBound?]; split
    · exact ihl H
    · next hv => exact ihr fun | rfl, e => nomatch hv.symm.trans e
    · next hv => intro | rfl, e => cases hv.symm.trans e

/-- The value `x` returned by `lowerBound?` is less or equal to the `cut`. -/
theorem lowerBound?_le {t : RBNode α} : t.lowerBound? cut none = some x → cut x ≠ .lt :=
  lowerBound?_le' nofun

theorem All.lowerBound?_lb {t : RBNode α} (hp : t.All p) (H : ∀ {x}, x ∈ lb → p x) :
    t.lowerBound? cut lb = some x → p x := by
  induction t generalizing lb with
  | nil => exact H
  | node _ _ _ _ ihl ihr =>
    simp [lowerBound?]; split
    · exact ihl hp.2.1 H
    · exact ihr hp.2.2 fun | rfl => hp.1
    · exact fun | rfl => hp.1

theorem All.lowerBound? {t : RBNode α} (hp : t.All p) : t.lowerBound? cut none = some x → p x :=
  hp.lowerBound?_lb nofun

theorem lowerBound?_mem_lb {t : RBNode α}
    (h : t.lowerBound? cut lb = some x) : x ∈ t ∨ x ∈ lb :=
  All.lowerBound?_lb (p := fun x => x ∈ t ∨ x ∈ lb) (All_def.2 fun _ => .inl) Or.inr h

theorem lowerBound?_mem {t : RBNode α} (h : t.lowerBound? cut none = some x) : x ∈ t :=
  (lowerBound?_mem_lb h).resolve_right nofun

theorem lowerBound?_of_some {t : RBNode α} : ∃ x, t.lowerBound? cut (some y) = some x := by
  induction t generalizing y <;> simp [lowerBound?]; split <;> simp [*]

theorem Ordered.lowerBound?_exists [@TransCmp α cmp] [IsCut cmp cut] (h : Ordered cmp t) :
    (∃ x, t.lowerBound? cut none = some x) ↔ ∃ x ∈ t, cut x ≠ .lt := by
  refine ⟨fun ⟨x, hx⟩ => ⟨_, lowerBound?_mem hx, lowerBound?_le hx⟩, fun H => ?_⟩
  obtain ⟨x, hx, e⟩ := H
  induction t generalizing x with
  | nil => cases hx
  | node _ _ _ _ ihl =>
    simp [lowerBound?]; split
    · rcases hx with rfl | hx | hx
      · contradiction
      · exact ihl h.2.2.1 _ hx e
      · next hv => cases e <| IsCut.lt_trans (All_def.1 h.2.1 _ hx).1 hv
    · exact lowerBound?_of_some
    · exact ⟨_, rfl⟩

theorem Ordered.lowerBound?_least_lb [@TransCmp α cmp] [IsCut cmp cut] (h : Ordered cmp t)
    (hlb : ∀ {x}, lb = some x → t.All (cmpLT cmp x ·)) :
    t.lowerBound? cut lb = some x → y ∈ t → cut x = .gt → cmp x y = .lt → cut y = .lt := by
  induction t generalizing lb with
  | nil => nofun
  | node _ _ _ _ ihl ihr =>
    simp [lowerBound?]; split <;> rename_i hv <;> rintro h₁ (rfl | hy' | hy') hx h₂
    · exact hv
    · exact ihl h.2.2.1 (fun h => (hlb h).2.1) h₁ hy' hx h₂
    · exact IsCut.lt_trans (cut := cut) (cmp := cmp) (All_def.1 h.2.1 _ hy').1 hv
    · rcases lowerBound?_mem_lb h₁ with h₁ | ⟨⟨⟩⟩
      · cases TransCmp.lt_asymm h₂ (All_def.1 h.2.1 _ h₁).1
      · cases TransCmp.lt_asymm h₂ h₂
    · refine (TransCmp.lt_asymm h₂ ?_).elim; have := (All_def.1 h.1 _ hy').1
      rcases lowerBound?_mem_lb h₁ with h₁ | ⟨⟨⟩⟩
      · exact TransCmp.lt_trans this (All_def.1 h.2.1 _ h₁).1
      · exact this
    · exact ihr h.2.2.2 (by rintro _ ⟨⟨⟩⟩; exact h.2.1) h₁ hy' hx h₂
    · cases h₁; cases TransCmp.lt_asymm h₂ h₂
    · cases h₁; cases hx.symm.trans hv
    · cases h₁; cases hx.symm.trans hv

/--
A statement of the least-ness of the result of `lowerBound?`. If `x` is the return value of
`lowerBound?` and it is strictly less than the cut, then any other `y > x` in the tree is in fact
strictly greater than the cut (so there is no exact match, and nothing closer to the cut).
-/
theorem Ordered.lowerBound?_least [@TransCmp α cmp] [IsCut cmp cut] (ht : Ordered cmp t)
    (H : t.lowerBound? cut none = some x) (hy : y ∈ t)
    (xy : cmp x y = .lt) (hx : cut x = .gt) : cut y = .lt :=
  ht.lowerBound?_least_lb (by nofun) H hy hx xy

theorem Ordered.memP_iff_lowerBound? [@TransCmp α cmp] [IsCut cmp cut] (ht : Ordered cmp t) :
    t.MemP cut ↔ ∃ x, t.lowerBound? cut none = some x ∧ cut x = .eq := by
  refine memP_def.trans ⟨fun ⟨y, hy, ey⟩ => ?_, fun ⟨x, hx, e⟩ => ⟨_, lowerBound?_mem hx, e⟩⟩
  have ⟨x, hx⟩ := ht.lowerBound?_exists.2 ⟨_, hy, fun h => nomatch ey.symm.trans h⟩
  refine ⟨x, hx, ?_⟩; cases ex : cut x
  · cases lowerBound?_le hx ex
  · rfl
  · cases e : cmp x y
    · cases ey.symm.trans <| ht.lowerBound?_least hx hy e ex
    · cases ey.symm.trans <| IsCut.congr e |>.symm.trans ex
    · cases ey.symm.trans <| IsCut.gt_trans (OrientedCmp.cmp_eq_gt.1 e) ex

/-- A stronger version of `lowerBound?_least` that holds when the cut is strict. -/
theorem Ordered.lowerBound?_lt [@TransCmp α cmp] [IsStrictCut cmp cut] (ht : Ordered cmp t)
    (H : t.lowerBound? cut none = some x) (hy : y ∈ t) : cmp x y = .lt ↔ cut y = .lt := by
  refine ⟨fun h => ?_, fun h => OrientedCmp.cmp_eq_gt.1 ?_⟩
  · cases e : cut x
    · cases lowerBound?_le H e
    · exact IsStrictCut.exact e |>.symm.trans h
    · exact ht.lowerBound?_least H hy h e
  · by_contra h'; exact lowerBound?_le H <| IsCut.le_lt_trans (cmp := cmp) (cut := cut) h' h

end lowerBound?

section fold

theorem foldr_cons (t : RBNode α) (l) : t.foldr (·::·) l = t.toList ++ l := by
  unfold toList
  induction t generalizing l with
  | nil => rfl
  | node _ a _ b iha ihb => rw [foldr, foldr, iha, iha (_::_), ihb]; simp

@[simp] theorem toList_nil : (.nil : RBNode α).toList = [] := rfl

@[simp] theorem toList_node : (.node c a x b : RBNode α).toList = a.toList ++ x :: b.toList := by
  rw [toList, foldr, foldr_cons]; rfl

@[simp] theorem toList_reverse (t : RBNode α) : t.reverse.toList = t.toList.reverse := by
  induction t <;> simp [*]

@[simp] theorem mem_toList {t : RBNode α} : x ∈ t.toList ↔ x ∈ t := by
  induction t <;> simp [*, or_left_comm]

@[simp] theorem mem_reverse {t : RBNode α} : a ∈ t.reverse ↔ a ∈ t := by rw [← mem_toList]; simp

theorem min?_eq_toList_head? {t : RBNode α} : t.min? = t.toList.head? := by
  induction t with
  | nil => rfl
  | node _ l _ _ ih =>
    cases l <;> simp [RBNode.min?, ih]
    next ll _ _ => cases toList ll <;> rfl

theorem max?_eq_toList_getLast? {t : RBNode α} : t.max? = t.toList.getLast? := by
  rw [← min?_reverse, min?_eq_toList_head?]; simp

theorem foldr_eq_foldr_toList {t : RBNode α} : t.foldr f init = t.toList.foldr f init := by
  induction t generalizing init <;> simp [*]

theorem foldl_eq_foldl_toList {t : RBNode α} : t.foldl f init = t.toList.foldl f init := by
  induction t generalizing init <;> simp [*]

theorem foldl_reverse {α β : Type _} {t : RBNode α} {f : β → α → β} {init : β} :
    t.reverse.foldl f init = t.foldr (flip f) init := by
  simp (config := {unfoldPartialApp := true})
    [foldr_eq_foldr_toList, foldl_eq_foldl_toList, flip]

theorem foldr_reverse {α β : Type _} {t : RBNode α} {f : α → β → β} {init : β} :
    t.reverse.foldr f init = t.foldl (flip f) init :=
  foldl_reverse.symm.trans (by simp; rfl)

theorem forM_eq_forM_toList [Monad m] [LawfulMonad m] {t : RBNode α} :
    t.forM (m := m) f = t.toList.forM f := by induction t <;> simp [*]

theorem foldlM_eq_foldlM_toList [Monad m] [LawfulMonad m] {t : RBNode α} :
    t.foldlM (m := m) f init = t.toList.foldlM f init := by
  induction t generalizing init <;> simp [*]

theorem forIn_visit_eq_bindList [Monad m] [LawfulMonad m] {t : RBNode α} :
    forIn.visit (m := m) f t init = (ForInStep.yield init).bindList f t.toList := by
  induction t generalizing init <;> simp [*, forIn.visit]

theorem forIn_eq_forIn_toList [Monad m] [LawfulMonad m] {t : RBNode α} :
    forIn (m := m) t init f = forIn t.toList init f := by
  conv => lhs; simp only [forIn, RBNode.forIn]
  rw [List.forIn_eq_bindList, forIn_visit_eq_bindList]

end fold

namespace Stream

attribute [simp] foldl foldr

theorem foldr_cons (t : RBNode.Stream α) (l) : t.foldr (·::·) l = t.toList ++ l := by
  unfold toList; apply Eq.symm; induction t <;> simp [*, foldr, RBNode.foldr_cons]

@[simp] theorem toList_nil : (.nil : RBNode.Stream α).toList = [] := rfl

@[simp] theorem toList_cons :
    (.cons x r s : RBNode.Stream α).toList = x :: r.toList ++ s.toList := by
  rw [toList, toList, foldr, RBNode.foldr_cons]; rfl

theorem foldr_eq_foldr_toList {s : RBNode.Stream α} : s.foldr f init = s.toList.foldr f init := by
  induction s <;> simp [*, RBNode.foldr_eq_foldr_toList]

theorem foldl_eq_foldl_toList {t : RBNode.Stream α} : t.foldl f init = t.toList.foldl f init := by
  induction t generalizing init <;> simp [*, RBNode.foldl_eq_foldl_toList]

theorem forIn_eq_forIn_toList [Monad m] [LawfulMonad m] {t : RBNode α} :
    forIn (m := m) t init f = forIn t.toList init f := by
  conv => lhs; simp only [forIn, RBNode.forIn]
  rw [List.forIn_eq_bindList, forIn_visit_eq_bindList]

end Stream

theorem toStream_toList' {t : RBNode α} {s} : (t.toStream s).toList = t.toList ++ s.toList := by
  induction t generalizing s <;> simp [*, toStream]

@[simp] theorem toStream_toList {t : RBNode α} : t.toStream.toList = t.toList := by
  simp [toStream_toList']

theorem Stream.next?_toList {s : RBNode.Stream α} :
    (s.next?.map fun (a, b) => (a, b.toList)) = s.toList.next? := by
  cases s <;> simp [next?, toStream_toList']

theorem ordered_iff {t : RBNode α} :
    t.Ordered cmp ↔ t.toList.Pairwise (cmpLT cmp) := by
  induction t with
  | nil => simp
  | node c l v r ihl ihr =>
    simp [*, List.pairwise_append, Ordered, All_def,
      and_assoc, and_left_comm, and_comm, imp_and, forall_and]
    exact fun _ _ hl hr a ha b hb => (hl _ ha).trans (hr _ hb)

theorem Ordered.toList_sorted {t : RBNode α} : t.Ordered cmp → t.toList.Pairwise (cmpLT cmp) :=
  ordered_iff.1

theorem min?_mem {t : RBNode α} (h : t.min? = some a) : a ∈ t := by
  rw [min?_eq_toList_head?] at h
  rw [← mem_toList]
  revert h; cases toList t <;> rintro ⟨⟩; constructor

theorem Ordered.min?_le {t : RBNode α} [TransCmp cmp] (ht : t.Ordered cmp) (h : t.min? = some a)
    (x) (hx : x ∈ t) : cmp a x ≠ .gt := by
  rw [min?_eq_toList_head?] at h
  rw [← mem_toList] at hx
  have := ht.toList_sorted
  revert h hx this; cases toList t <;> rintro ⟨⟩ (_ | ⟨_, hx⟩) (_ | ⟨h1,h2⟩)
  · rw [OrientedCmp.cmp_refl (cmp := cmp)]; decide
  · rw [(h1 _ hx).1]; decide

theorem max?_mem {t : RBNode α} (h : t.max? = some a) : a ∈ t := by
  simpa using min?_mem ((min?_reverse _).trans h)

theorem Ordered.le_max? {t : RBNode α} [TransCmp cmp] (ht : t.Ordered cmp) (h : t.max? = some a)
    (x) (hx : x ∈ t) : cmp x a ≠ .gt :=
  ht.reverse.min?_le ((min?_reverse _).trans h) _ (by simpa using hx)

@[simp] theorem setBlack_toList {t : RBNode α} : t.setBlack.toList = t.toList := by
  cases t <;> simp [setBlack]

@[simp] theorem setRed_toList {t : RBNode α} : t.setRed.toList = t.toList := by
  cases t <;> simp [setRed]

@[simp] theorem balance1_toList {l : RBNode α} {v r} :
    (l.balance1 v r).toList = l.toList ++ v :: r.toList := by
  unfold balance1; split <;> simp

@[simp] theorem balance2_toList {l : RBNode α} {v r} :
    (l.balance2 v r).toList = l.toList ++ v :: r.toList := by
  unfold balance2; split <;> simp

@[simp] theorem balLeft_toList {l : RBNode α} {v r} :
    (l.balLeft v r).toList = l.toList ++ v :: r.toList := by
  unfold balLeft; split <;> (try simp); split <;> simp

@[simp] theorem balRight_toList {l : RBNode α} {v r} :
    (l.balRight v r).toList = l.toList ++ v :: r.toList := by
  unfold balRight; split <;> (try simp); split <;> simp

theorem size_eq {t : RBNode α} : t.size = t.toList.length := by
  induction t <;> simp [*, size]; rfl

@[simp] theorem reverse_size (t : RBNode α) : t.reverse.size = t.size := by simp [size_eq]

@[simp] theorem find?_reverse (t : RBNode α) (cut : α → Ordering) :
    t.reverse.find? cut = t.find? (cut · |>.swap) := by
  induction t <;> simp [*, find?]
  cases cut _ <;> simp [Ordering.swap]

/--
Auxiliary definition for `zoom_ins`: set the root of the tree to `v`, creating a node if necessary.
-/
def setRoot (v : α) : RBNode α → RBNode α
  | nil => node red nil v nil
  | node c a _ b => node c a v b

/--
Auxiliary definition for `zoom_ins`: set the root of the tree to `v`, creating a node if necessary.
-/
def delRoot : RBNode α → RBNode α
  | nil => nil
  | node _ a _ b => a.append b

namespace Path

attribute [simp] RootOrdered Ordered

/-- The list of elements to the left of the hole.
(This function is intended for specification purposes only.) -/
@[simp] def listL : Path α → List α
  | .root => []
  | .left _ parent _ _ => parent.listL
  | .right _ l v parent => parent.listL ++ (l.toList ++ [v])

/-- The list of elements to the right of the hole.
(This function is intended for specification purposes only.) -/
@[simp] def listR : Path α → List α
  | .root => []
  | .left _ parent v r => v :: r.toList ++ parent.listR
  | .right _ _ _ parent => parent.listR

/-- Wraps a list of elements with the left and right elements of the path. -/
abbrev withList (p : Path α) (l : List α) : List α := p.listL ++ l ++ p.listR

theorem rootOrdered_iff {p : Path α} (hp : p.Ordered cmp) :
    p.RootOrdered cmp v ↔ (∀ a ∈ p.listL, cmpLT cmp a v) ∧ (∀ a ∈ p.listR, cmpLT cmp v a) := by
  induction p with
    (simp [All_def] at hp; simp [*, and_assoc, and_left_comm, and_comm, or_imp, forall_and])
  | left _ _ x _ ih => exact fun vx _ _ _ ha => vx.trans (hp.2.1 _ ha)
  | right _ _ x _ ih => exact fun xv _ _ _ ha => (hp.2.1 _ ha).trans xv

theorem ordered_iff {p : Path α} :
    p.Ordered cmp ↔ p.listL.Pairwise (cmpLT cmp) ∧ p.listR.Pairwise (cmpLT cmp) ∧
      ∀ x ∈ p.listL, ∀ y ∈ p.listR, cmpLT cmp x y := by
  induction p with
  | root => simp
  | left _ _ x _ ih | right _ _ x _ ih => ?_
  all_goals
    rw [Ordered, and_congr_right_eq fun h => by simp [All_def, rootOrdered_iff h]; rfl]
    simp [List.pairwise_append, or_imp, forall_and, ih, RBNode.ordered_iff]
    -- FIXME: simp [and_assoc, and_left_comm, and_comm] is really slow here
  · exact ⟨
      fun ⟨⟨hL, hR, LR⟩, xr, ⟨Lx, xR⟩, ⟨rL, rR⟩, hr⟩ =>
        ⟨hL, ⟨⟨xr, xR⟩, hr, hR, rR⟩, Lx, fun _ ha _ hb => rL _ hb _ ha, LR⟩,
      fun ⟨hL, ⟨⟨xr, xR⟩, hr, hR, rR⟩, Lx, Lr, LR⟩ =>
        ⟨⟨hL, hR, LR⟩, xr, ⟨Lx, xR⟩, ⟨fun _ ha _ hb => Lr _ hb _ ha, rR⟩, hr⟩⟩
  · exact ⟨
      fun ⟨⟨hL, hR, LR⟩, lx, ⟨Lx, xR⟩, ⟨lL, lR⟩, hl⟩ =>
        ⟨⟨hL, ⟨hl, lx⟩, fun _ ha _ hb => lL _ hb _ ha, Lx⟩, hR, LR, lR, xR⟩,
      fun ⟨⟨hL, ⟨hl, lx⟩, Ll, Lx⟩, hR, LR, lR, xR⟩ =>
       ⟨⟨hL, hR, LR⟩, lx, ⟨Lx, xR⟩, ⟨fun _ ha _ hb => Ll _ hb _ ha, lR⟩, hl⟩⟩

theorem zoom_zoomed₁ (e : zoom cut t path = (t', path')) : t'.OnRoot (cut · = .eq) :=
  match t, e with
  | nil, rfl => trivial
  | node .., e => by
    revert e; unfold zoom; split
    · exact zoom_zoomed₁
    · exact zoom_zoomed₁
    · next H => intro e; cases e; exact H

@[simp] theorem fill_toList {p : Path α} : (p.fill t).toList = p.withList t.toList := by
  induction p generalizing t <;> simp [*]

theorem _root_.Batteries.RBNode.zoom_toList {t : RBNode α} (eq : t.zoom cut = (t', p')) :
    p'.withList t'.toList = t.toList := by rw [← fill_toList, ← zoom_fill eq]; rfl

@[simp] theorem ins_toList {p : Path α} : (p.ins t).toList = p.withList t.toList := by
  match p with
  | .root | .left red .. | .right red .. | .left black .. | .right black .. =>
    simp [ins, ins_toList]

@[simp] theorem insertNew_toList {p : Path α} : (p.insertNew v).toList = p.withList [v] := by
  simp [insertNew]

theorem insert_toList {p : Path α} :
    (p.insert t v).toList = p.withList (t.setRoot v).toList := by
  simp [insert]; split <;> simp [setRoot]

protected theorem Balanced.insert {path : Path α} (hp : path.Balanced c₀ n₀ c n) :
    t.Balanced c n → ∃ c n, (path.insert t v).Balanced c n
  | .nil => ⟨_, hp.insertNew⟩
  | .red ha hb => ⟨_, _, hp.fill (.red ha hb)⟩
  | .black ha hb => ⟨_, _, hp.fill (.black ha hb)⟩

theorem Ordered.insert : ∀ {path : Path α} {t : RBNode α},
    path.Ordered cmp → t.Ordered cmp → t.All (path.RootOrdered cmp) → path.RootOrdered cmp v →
    t.OnRoot (cmpEq cmp v) → (path.insert t v).Ordered cmp
  | _, nil, hp, _, _, vp, _ => hp.insertNew vp
  | _, node .., hp, ⟨ax, xb, ha, hb⟩, ⟨_, ap, bp⟩, vp, xv => Ordered.fill.2
    ⟨hp, ⟨ax.imp xv.lt_congr_right.2, xb.imp xv.lt_congr_left.2, ha, hb⟩, vp, ap, bp⟩

theorem Ordered.erase : ∀ {path : Path α} {t : RBNode α},
    path.Ordered cmp → t.Ordered cmp → t.All (path.RootOrdered cmp) → (path.erase t).Ordered cmp
  | _, nil, hp, ht, tp => Ordered.fill.2 ⟨hp, ht, tp⟩
  | _, node .., hp, ⟨ax, xb, ha, hb⟩, ⟨_, ap, bp⟩ => hp.del (ha.append ax xb hb) (ap.append bp)

theorem zoom_ins {t : RBNode α} {cmp : α → α → Ordering} :
    t.zoom (cmp v) path = (t', path') →
    path.ins (t.ins cmp v) = path'.ins (t'.setRoot v) := by
  unfold RBNode.ins; split <;> simp [zoom]
  · intro | rfl, rfl => rfl
  all_goals
  · split
    · exact zoom_ins
    · exact zoom_ins
    · intro | rfl => rfl

theorem insertNew_eq_insert (h : zoom (cmp v) t = (nil, path)) :
    path.insertNew v = (t.insert cmp v).setBlack :=
  insert_setBlack .. ▸ (zoom_ins h).symm

theorem ins_eq_fill {path : Path α} {t : RBNode α} :
    path.Balanced c₀ n₀ c n → t.Balanced c n → path.ins t = (path.fill t).setBlack
  | .root, h => rfl
  | .redL hb H, ha | .redR ha H, hb => by unfold ins; exact ins_eq_fill H (.red ha hb)
  | .blackL hb H, ha => by rw [ins, fill, ← ins_eq_fill H (.black ha hb), balance1_eq ha]
  | .blackR ha H, hb => by rw [ins, fill, ← ins_eq_fill H (.black ha hb), balance2_eq hb]

theorem zoom_insert {path : Path α} {t : RBNode α} (ht : t.Balanced c n)
    (H : zoom (cmp v) t = (t', path)) :
    (path.insert t' v).setBlack = (t.insert cmp v).setBlack := by
  have ⟨_, _, ht', hp'⟩ := ht.zoom .root H
  cases ht' with simp [insert]
  | nil => simp [insertNew_eq_insert H, setBlack_idem]
  | red hl hr => rw [← ins_eq_fill hp' (.red hl hr), insert_setBlack]; exact (zoom_ins H).symm
  | black hl hr => rw [← ins_eq_fill hp' (.black hl hr), insert_setBlack]; exact (zoom_ins H).symm

theorem zoom_del {t : RBNode α} :
    t.zoom cut path = (t', path') →
    path.del (t.del cut) (match t with | node c .. => c | _ => red) =
    path'.del t'.delRoot (match t' with | node c .. => c | _ => red) := by
  unfold RBNode.del; split <;> simp [zoom]
  · intro | rfl, rfl => rfl
  · next c a y b =>
    split
    · have IH := @zoom_del (t := a)
      match a with
      | nil => intro | rfl => rfl
      | node black .. | node red .. => apply IH
    · have IH := @zoom_del (t := b)
      match b with
      | nil => intro | rfl => rfl
      | node black .. | node red .. => apply IH
    · intro | rfl => rfl

/-- Asserts that `p` holds on all elements to the left of the hole. -/
def AllL (p : α → Prop) : Path α → Prop
  | .root => True
  | .left _ parent _ _ => parent.AllL p
  | .right _ a x parent => a.All p ∧ p x ∧ parent.AllL p

/-- Asserts that `p` holds on all elements to the right of the hole. -/
def AllR (p : α → Prop) : Path α → Prop
  | .root => True
  | .left _ parent x b => parent.AllR p ∧ p x ∧ b.All p
  | .right _ _ _ parent => parent.AllR p

end Path

theorem insert_toList_zoom {t : RBNode α} (ht : Balanced t c n)
    (e : zoom (cmp v) t = (t', p)) :
    (t.insert cmp v).toList = p.withList (t'.setRoot v).toList := by
  rw [← setBlack_toList, ← Path.zoom_insert ht e, setBlack_toList, Path.insert_toList]

theorem insert_toList_zoom_nil {t : RBNode α} (ht : Balanced t c n)
    (e : zoom (cmp v) t = (nil, p)) :
    (t.insert cmp v).toList = p.withList [v] := insert_toList_zoom ht e

theorem exists_insert_toList_zoom_nil {t : RBNode α} (ht : Balanced t c n)
    (e : zoom (cmp v) t = (nil, p)) :
    ∃ L R, t.toList = L ++ R ∧ (t.insert cmp v).toList = L ++ v :: R :=
  ⟨p.listL, p.listR, by simp [← zoom_toList e, insert_toList_zoom_nil ht e]⟩

theorem insert_toList_zoom_node {t : RBNode α} (ht : Balanced t c n)
    (e : zoom (cmp v) t = (node c' l v' r, p)) :
    (t.insert cmp v).toList = p.withList (node c l v r).toList := insert_toList_zoom ht e

theorem exists_insert_toList_zoom_node {t : RBNode α} (ht : Balanced t c n)
    (e : zoom (cmp v) t = (node c' l v' r, p)) :
    ∃ L R, t.toList = L ++ v' :: R ∧ (t.insert cmp v).toList = L ++ v :: R := by
  refine ⟨p.listL ++ l.toList, r.toList ++ p.listR, ?_⟩
  simp [← zoom_toList e, insert_toList_zoom_node ht e]

theorem mem_insert_self {t : RBNode α} (ht : Balanced t c n) : v ∈ t.insert cmp v := by
  rw [← mem_toList, List.mem_iff_append]
  exact match e : zoom (cmp v) t with
  | (nil, p) => let ⟨_, _, _, h⟩ := exists_insert_toList_zoom_nil ht e; ⟨_, _, h⟩
  | (node .., p) => let ⟨_, _, _, h⟩ := exists_insert_toList_zoom_node ht e; ⟨_, _, h⟩

theorem mem_insert_of_mem {t : RBNode α} (ht : Balanced t c n) (h : v' ∈ t) :
    v' ∈ t.insert cmp v ∨ cmp v v' = .eq := by
  match e : zoom (cmp v) t with
  | (nil, p) =>
    let ⟨_, _, h₁, h₂⟩ := exists_insert_toList_zoom_nil ht e
    simp [← mem_toList, h₁] at h
    simp [← mem_toList, h₂]; cases h <;> simp [*]
  | (node .., p) =>
    let ⟨_, _, h₁, h₂⟩ := exists_insert_toList_zoom_node ht e
    simp [← mem_toList, h₁] at h
    simp [← mem_toList, h₂]; rcases h with h|h|h <;> simp [*]
    exact .inr (Path.zoom_zoomed₁ e)

theorem exists_find?_insert_self [@TransCmp α cmp] [IsCut cmp cut]
    {t : RBNode α} (ht : Balanced t c n) (ht₂ : Ordered cmp t) (hv : cut v = .eq) :
    ∃ x, (t.insert cmp v).find? cut = some x :=
  ht₂.insert.memP_iff_find?.1 <| memP_def.2 ⟨_, mem_insert_self ht, hv⟩

theorem find?_insert_self [@TransCmp α cmp] [IsStrictCut cmp cut]
    {t : RBNode α} (ht : Balanced t c n) (ht₂ : Ordered cmp t) (hv : cut v = .eq) :
    (t.insert cmp v).find? cut = some v :=
  ht₂.insert.find?_some.2 ⟨mem_insert_self ht, hv⟩

theorem mem_insert [@TransCmp α cmp] {t : RBNode α} (ht : Balanced t c n) (ht₂ : Ordered cmp t) :
    v' ∈ t.insert cmp v ↔ (v' ∈ t ∧ t.find? (cmp v) ≠ some v') ∨ v' = v := by
  refine ⟨fun h => ?_, fun | .inl ⟨h₁, h₂⟩ => ?_ | .inr h => ?_⟩
  · match e : zoom (cmp v) t with
    | (nil, p) =>
      let ⟨_, _, h₁, h₂⟩ := exists_insert_toList_zoom_nil ht e
      simp [← mem_toList, h₂] at h; rw [← or_assoc, or_right_comm] at h
      refine h.imp_left fun h => ?_
      simp [← mem_toList, h₁, h]
      rw [find?_eq_zoom, e]; nofun
    | (node .., p) =>
      let ⟨_, _, h₁, h₂⟩ := exists_insert_toList_zoom_node ht e
      simp [← mem_toList, h₂] at h; simp [← mem_toList, h₁]; rw [or_left_comm] at h ⊢
      rcases h with _|h <;> simp [*]
      refine .inl fun h => ?_
      rw [find?_eq_zoom, e] at h; cases h
      suffices cmpLT cmp v' v' by cases OrientedCmp.cmp_refl.symm.trans this.1
      have := ht₂.toList_sorted; simp [h₁, List.pairwise_append] at this
      exact h.elim (this.2.2 _ · |>.1) (this.2.1.1 _)
  · exact (mem_insert_of_mem ht h₁).resolve_right fun h' => h₂ <| ht₂.find?_some.2 ⟨h₁, h'⟩
  · exact h ▸ mem_insert_self ht

end RBNode

open RBNode (IsCut IsStrictCut)

namespace RBSet

@[simp] theorem val_toList {t : RBSet α cmp} : t.1.toList = t.toList := rfl

@[simp] theorem mkRBSet_eq : mkRBSet α cmp = ∅ := rfl
@[simp] theorem empty_eq : @RBSet.empty α cmp = ∅ := rfl
@[simp] theorem default_eq : (default : RBSet α cmp) = ∅ := rfl
@[simp] theorem empty_toList : toList (∅ : RBSet α cmp) = [] := rfl
@[simp] theorem single_toList : toList (single a : RBSet α cmp) = [a] := rfl

theorem mem_toList {t : RBSet α cmp} : x ∈ toList t ↔ x ∈ t.1 := RBNode.mem_toList

theorem mem_congr [@TransCmp α cmp] {t : RBSet α cmp} (h : cmp x y = .eq) : x ∈ t ↔ y ∈ t :=
  RBNode.mem_congr h

theorem mem_iff_mem_toList {t : RBSet α cmp} : x ∈ t ↔ ∃ y ∈ toList t, cmp x y = .eq :=
  RBNode.mem_def.trans <| by simp [mem_toList]

theorem mem_of_mem_toList [@OrientedCmp α cmp] {t : RBSet α cmp} (h : x ∈ toList t) : x ∈ t :=
  mem_iff_mem_toList.2 ⟨_, h, OrientedCmp.cmp_refl⟩

theorem foldl_eq_foldl_toList {t : RBSet α cmp} : t.foldl f init = t.toList.foldl f init :=
  RBNode.foldl_eq_foldl_toList

theorem foldr_eq_foldr_toList {t : RBSet α cmp} : t.foldr f init = t.toList.foldr f init :=
  RBNode.foldr_eq_foldr_toList

theorem foldlM_eq_foldlM_toList [Monad m] [LawfulMonad m] {t : RBSet α cmp} :
    t.foldlM (m := m) f init = t.toList.foldlM f init := RBNode.foldlM_eq_foldlM_toList

theorem forM_eq_forM_toList [Monad m] [LawfulMonad m] {t : RBSet α cmp} :
    t.forM (m := m) f = t.toList.forM f := RBNode.forM_eq_forM_toList

theorem forIn_eq_forIn_toList [Monad m] [LawfulMonad m] {t : RBSet α cmp} :
    forIn (m := m) t init f = forIn t.toList init f := RBNode.forIn_eq_forIn_toList

theorem toStream_eq {t : RBSet α cmp} : toStream t = t.1.toStream .nil := rfl

@[simp] theorem toStream_toList {t : RBSet α cmp} : (toStream t).toList = t.toList := by
  simp [toStream_eq]

theorem isEmpty_iff_toList_eq_nil {t : RBSet α cmp} :
    t.isEmpty ↔ t.toList = [] := by obtain ⟨⟨⟩, _⟩ := t <;> simp [toList, isEmpty]

theorem toList_sorted {t : RBSet α cmp} : t.toList.Pairwise (RBNode.cmpLT cmp) :=
  t.2.out.1.toList_sorted

theorem findP?_some_eq_eq {t : RBSet α cmp} : t.findP? cut = some y → cut y = .eq :=
  RBNode.find?_some_eq_eq

theorem find?_some_eq_eq {t : RBSet α cmp} : t.find? x = some y → cmp x y = .eq :=
  findP?_some_eq_eq

theorem findP?_some_mem_toList {t : RBSet α cmp} (h : t.findP? cut = some y) : y ∈ toList t :=
  mem_toList.2 <| RBNode.find?_some_mem h

theorem find?_some_mem_toList {t : RBSet α cmp} (h : t.find? x = some y) : y ∈ toList t :=
  findP?_some_mem_toList h

theorem findP?_some_memP {t : RBSet α cmp} (h : t.findP? cut = some y) : t.MemP cut :=
  RBNode.find?_some_memP h

theorem find?_some_mem {t : RBSet α cmp} (h : t.find? x = some y) : x ∈ t :=
  findP?_some_memP h

theorem mem_toList_unique [@TransCmp α cmp] {t : RBSet α cmp}
    (hx : x ∈ toList t) (hy : y ∈ toList t) (e : cmp x y = .eq) : x = y :=
  t.2.out.1.unique (mem_toList.1 hx) (mem_toList.1 hy) e

theorem findP?_some [@TransCmp α cmp] [IsStrictCut cmp cut] {t : RBSet α cmp} :
    t.findP? cut = some y ↔ y ∈ toList t ∧ cut y = .eq :=
  t.2.out.1.find?_some.trans <| by simp [mem_toList]

theorem find?_some [@TransCmp α cmp] {t : RBSet α cmp} :
    t.find? x = some y ↔ y ∈ toList t ∧ cmp x y = .eq := findP?_some

theorem memP_iff_findP? [@TransCmp α cmp] [IsCut cmp cut] {t : RBSet α cmp} :
    MemP cut t ↔ ∃ y, t.findP? cut = some y := t.2.out.1.memP_iff_find?

theorem mem_iff_find? [@TransCmp α cmp] {t : RBSet α cmp} :
    x ∈ t ↔ ∃ y, t.find? x = some y := memP_iff_findP?

@[simp] theorem contains_iff [@TransCmp α cmp] {t : RBSet α cmp} :
    t.contains x ↔ x ∈ t := Option.isSome_iff_exists.trans mem_iff_find?.symm

instance [@TransCmp α cmp] {t : RBSet α cmp} : Decidable (x ∈ t) := decidable_of_iff _ contains_iff

theorem size_eq (t : RBSet α cmp) : t.size = t.toList.length := RBNode.size_eq

theorem mem_toList_insert_self (v) (t : RBSet α cmp) : v ∈ toList (t.insert v) :=
  let ⟨_, _, h⟩ := t.2.out.2; mem_toList.2 (RBNode.mem_insert_self h)

theorem mem_insert_self [@OrientedCmp α cmp] (v) (t : RBSet α cmp) : v ∈ t.insert v :=
  mem_of_mem_toList <| mem_toList_insert_self v t

theorem mem_insert_of_eq [@TransCmp α cmp] (t : RBSet α cmp) (h : cmp v v' = .eq) :
    v' ∈ t.insert v := (mem_congr h).1 (mem_insert_self ..)

theorem mem_toList_insert_of_mem (v) {t : RBSet α cmp} (h : v' ∈ toList t) :
    v' ∈ toList (t.insert v) ∨ cmp v v' = .eq :=
  let ⟨_, _, ht⟩ := t.2.out.2
  .imp_left mem_toList.2 <| RBNode.mem_insert_of_mem ht <| mem_toList.1 h

theorem mem_insert_of_mem_toList [@OrientedCmp α cmp] (v) {t : RBSet α cmp} (h : v' ∈ toList t) :
    v' ∈ t.insert v :=
  match mem_toList_insert_of_mem v h with
  | .inl h' => mem_of_mem_toList h'
  | .inr h' => mem_iff_mem_toList.2 ⟨_, mem_toList_insert_self .., OrientedCmp.cmp_eq_eq_symm.1 h'⟩

theorem mem_insert_of_mem [@TransCmp α cmp] (v) {t : RBSet α cmp} (h : v' ∈ t) : v' ∈ t.insert v :=
  let ⟨_, h₁, h₂⟩ := mem_iff_mem_toList.1 h
  (mem_congr h₂).2 (mem_insert_of_mem_toList v h₁)

theorem mem_toList_insert [@TransCmp α cmp] {t : RBSet α cmp} :
    v' ∈ toList (t.insert v) ↔ (v' ∈ toList t ∧ t.find? v ≠ some v') ∨ v' = v := by
  let ⟨ht₁, _, _, ht₂⟩ := t.2.out
  simpa [mem_toList] using RBNode.mem_insert ht₂ ht₁

theorem mem_insert [@TransCmp α cmp] {t : RBSet α cmp} :
    v' ∈ t.insert v ↔ v' ∈ t ∨ cmp v v' = .eq := by
  refine ⟨fun h => ?_, fun | .inl h => mem_insert_of_mem _ h | .inr h => mem_insert_of_eq _ h⟩
  let ⟨_, h₁, h₂⟩ := mem_iff_mem_toList.1 h
  match mem_toList_insert.1 h₁ with
  | .inl ⟨h₃, _⟩ => exact .inl <| mem_iff_mem_toList.2 ⟨_, h₃, h₂⟩
  | .inr rfl => exact .inr <| OrientedCmp.cmp_eq_eq_symm.1 h₂

theorem find?_congr [@TransCmp α cmp] (t : RBSet α cmp) (h : cmp v₁ v₂ = .eq) :
    t.find? v₁ = t.find? v₂ := by simp [find?, TransCmp.cmp_congr_left' h]

theorem findP?_insert_of_eq [@TransCmp α cmp] [IsStrictCut cmp cut]
    (t : RBSet α cmp) (h : cut v = .eq) : (t.insert v).findP? cut = some v :=
  findP?_some.2 ⟨mem_toList_insert_self .., h⟩

theorem find?_insert_of_eq [@TransCmp α cmp] (t : RBSet α cmp) (h : cmp v' v = .eq) :
    (t.insert v).find? v' = some v := findP?_insert_of_eq t h

theorem findP?_insert_of_ne [@TransCmp α cmp] [IsStrictCut cmp cut]
    (t : RBSet α cmp) (h : cut v ≠ .eq) : (t.insert v).findP? cut = t.findP? cut := by
  refine Option.ext fun u =>
    findP?_some.trans <| .trans (and_congr_left fun h' => ?_) findP?_some.symm
  rw [mem_toList_insert, or_iff_left, and_iff_left]
  · exact mt (fun h => by rwa [IsCut.congr (cut := cut) (find?_some_eq_eq h)]) h
  · rintro rfl; contradiction

theorem find?_insert_of_ne [@TransCmp α cmp] (t : RBSet α cmp) (h : cmp v' v ≠ .eq) :
    (t.insert v).find? v' = t.find? v' := findP?_insert_of_ne t h

theorem findP?_insert [@TransCmp α cmp] (t : RBSet α cmp) (v cut) [IsStrictCut cmp cut] :
    (t.insert v).findP? cut = if cut v = .eq then some v else t.findP? cut := by
  split <;> [exact findP?_insert_of_eq t ‹_›; exact findP?_insert_of_ne t ‹_›]

theorem find?_insert [@TransCmp α cmp] (t : RBSet α cmp) (v v') :
    (t.insert v).find? v' = if cmp v' v = .eq then some v else t.find? v' := findP?_insert ..

end RBSet

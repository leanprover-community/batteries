/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Mario Carneiro
-/
import Std.Order
import Std.Logic
import Std.Tactic.ShowTerm

/-!
# Red-black trees

This module implements a type `RBMap α β cmp` which is a functional data structure for
storing a key-value store in a binary search tree.

It is built on the simpler `RBTree α cmp` type, which stores a set of values of type `α`
using the function `cmp : α → α → Ordering` for determining the ordering relation.
The tree will never store two elements that compare `.eq` under the `cmp` function,
but the function does not have to satisfy `cmp x y = .eq → x = y`, and in the map case
`α` is a key-value pair and the `cmp` function only compares the keys.
-/

namespace Std
namespace New -- TODO: lean4#1645

/--
In a red-black tree, every node has a color which is either "red" or "black"
(this particular choice of colors is conventional). A nil node is considered black.
-/
inductive RBColor where
  /-- A red node is required to have black children. -/
  | red
  /-- Every path from the root to a leaf must pass through the same number of black nodes. -/
  | black

/--
A red-black tree. (This is an internal implementation detail of the `RBTree` type,
which includes the invariants of the tree.) This is a binary search tree augmented with
a "color" field which is either red or black for each node and used to implement
the re-balancing operations.
See: [Red–black tree](https://en.wikipedia.org/wiki/Red%E2%80%93black_tree)
-/
inductive RBNode (α : Type u) where
  /-- An empty tree. -/
  | nil
  /-- A node consists of a value `v`, a subtree `l` of smaller items,
  and a subtree `r` of larger items. The color `c` is either `red` or `black`
  and participates in the red-black balance invariant (see `Balanced`). -/
  | node (c : RBColor) (l : RBNode α) (v : α) (r : RBNode α)

namespace RBNode
open RBColor

/-- The minimum element of a tree is the left-most value. -/
protected def min : RBNode α → Option α
  | nil            => none
  | node _ nil v _ => some v
  | node _ l _ _   => l.min

/-- The maximum element of a tree is the right-most value. -/
protected def max : RBNode α → Option α
  | nil            => none
  | node _ _ v nil => some v
  | node _ _ _ r   => r.max

/--
Fold a function in tree order along the nodes. `v₀` is used at `nil` nodes and
`f` is used to combine results at branching nodes.
-/
@[specialize] def fold (v₀ : σ) (f : σ → α → σ → σ) : RBNode α → σ
  | nil          => v₀
  | node _ l v r => f (l.fold v₀ f) v (r.fold v₀ f)

/-- Fold a function on the values from left to right (in increasing order). -/
@[specialize] def foldl (f : σ → α → σ) : (init : σ) → RBNode α → σ
  | b, nil          => b
  | b, node _ l v r => foldl f (f (foldl f b l) v) r

/-- Run monadic function `f` on each element of the tree (in increasing order). -/
@[specialize] def forM [Monad m] (f : α → m Unit) : RBNode α → m Unit
  | nil          => pure ()
  | node _ l v r => do forM f l; f v; forM f r

/-- Fold a monadic function on the values from left to right (in increasing order). -/
@[specialize] def foldlM [Monad m] (f : σ → α → m σ) : (init : σ) → RBNode α → m σ
  | b, nil          => pure b
  | b, node _ l v r => do foldlM f (← f (← foldlM f b l) v) r

/-- Implementation of `for x in t` loops over a `RBNode` (in increasing order). -/
@[inline] protected def forIn [Monad m]
    (as : RBNode α) (init : σ) (f : α → σ → m (ForInStep σ)) : m σ := do
  match ← visit as init with
  | .done b  => pure b
  | .yield b => pure b
where
  /-- Inner loop of `forIn`. -/
  @[specialize] visit : RBNode α → σ → m (ForInStep σ)
    | nil,          b => return ForInStep.yield b
    | node _ l v r, b => do
      match ← visit l b with
      | r@(.done _) => return r
      | .yield b    =>
        match ← f v b with
        | r@(.done _) => return r
        | .yield b    => visit r b

/-- Fold a function on the values from right to left (in decreasing order). -/
@[specialize] def foldr (f : α → σ → σ) : RBNode α → (init : σ) → σ
  | nil,          b => b
  | node _ l v r, b => l.foldr f (f v (r.foldr f b))

/-- Returns `true` iff every element of the tree satisfies `p`. -/
@[specialize] def all (p : α → Bool) : RBNode α → Bool
  | nil          => true
  | node _ l v r => p v && all p l && all p r

/-- Returns `true` iff any element of the tree satisfies `p`. -/
@[specialize] def any (p : α → Bool) : RBNode α → Bool
  | nil          => false
  | node _ l v r => p v || any p l || any p r

/-- Asserts that `p` holds on every element of the tree. -/
@[simp] def All (p : α → Prop) : RBNode α → Prop
  | nil          => True
  | node _ l v r => p v ∧ All p l ∧ All p r

theorem All.imp (H : ∀ {x : α}, p x → q x) : ∀ {t : RBNode α}, t.All p → t.All q
  | nil => id
  | node .. => fun ⟨h, hl, hr⟩ => ⟨H h, hl.imp H, hr.imp H⟩

/-- Asserts that `p` holds on some element of the tree. -/
@[simp] def Any (p : α → Prop) : RBNode α → Prop
  | nil          => False
  | node _ l v r => p v ∨ Any p l ∨ Any p r

/--
The red-black balance invariant. `Balanced t c n` says that the color of the root node is `c`,
and the black-height (the number of black nodes on any path from the root) of the tree is `n`.
Additionally, every red node must have black children.
-/
inductive Balanced : RBNode α → RBColor → Nat → Prop where
  /-- A nil node is balanced with black-height 0, and it is considered black. -/
  | protected nil : Balanced nil black 0
  /-- A red node is balanced with black-height `n`
  if its children are both black with with black-height `n`. -/
  | protected red : Balanced x black n → Balanced y black n → Balanced (node red x v y) red n
  /-- A black node is balanced with black-height `n + 1`
  if its children both have black-height `n`. -/
  | protected black : Balanced x c₁ n → Balanced y c₂ n → Balanced (node black x v y) black (n + 1)

/--
We say that `x < y` under the comparator `cmp` if `cmp x y = .lt`.

* In order to avoid assuming the comparator is always lawful, we use a
  local `∀ [TransCmp cmp]` binder in the relation so that the ordering
  properties of the tree only need to hold if the comparator is lawful.
* The `Nonempty` wrapper is a no-op because this is already a proposition,
  but it prevents the `[TransCmp cmp]` binder from being introduced when we don't want it.
-/
def cmpLt (cmp : α → α → Ordering) (x y : α) : Prop := Nonempty (∀ [TransCmp cmp], cmp x y = .lt)

theorem cmpLt.trans (h₁ : cmpLt cmp x y) (h₂ : cmpLt cmp y z) : cmpLt cmp x z :=
  ⟨TransCmp.lt_trans h₁.1 h₂.1⟩

theorem cmpLt.trans_l {cmp x y} (H : cmpLt cmp x y) {t : RBNode α}
    (h : t.All (cmpLt cmp y ·)) : t.All (cmpLt cmp x ·) := h.imp fun h => H.trans h

theorem cmpLt.trans_r {cmp x y} (H : cmpLt cmp x y) {a : RBNode α}
    (h : a.All (cmpLt cmp · x)) : a.All (cmpLt cmp · y) := h.imp fun h => h.trans H

/--
The ordering invariant of a red-black tree, which is a binary search tree.
This says that every element of a left subtree is less than the root, and
every element in the right subtree is greater than the root, where the
less than relation `x < y` is understood to mean `cmp x y = .lt`.

Because we do not assume that `cmp` is lawful when stating this property,
we write it in such a way that if `cmp` is not lawful then the condition holds trivially.
That way we can prove the ordering invariants without assuming `cmp` is lawful.
-/
def Ordered (cmp : α → α → Ordering) : RBNode α → Prop
  | nil => True
  | node _ a x b => a.All (cmpLt cmp · x) ∧ b.All (cmpLt cmp x ·) ∧ a.Ordered cmp ∧ b.Ordered cmp

/-- The first half of Okasaki's `balance`, concerning red-red sequences in the left child. -/
@[inline] def balance1 : RBNode α → α → RBNode α → RBNode α
  | node red (node red a x b) y c, z, d
  | node red a x (node red b y c), z, d => node red (node black a x b) y (node black c z d)
  | a,                             x, b => node black a x b

/-- The `balance1` function preserves the ordering invariants. -/
protected theorem Ordered.balance1 {l : RBNode α} {v : α} {r : RBNode α}
    (lv : l.All (cmpLt cmp · v)) (vr : r.All (cmpLt cmp v ·))
    (hl : l.Ordered cmp) (hr : r.Ordered cmp) : (balance1 l v r).Ordered cmp := by
  unfold balance1; split
  case _ a x b y c =>
    have ⟨yv, _, cv⟩ := lv; have ⟨xy, yc, hx, hc⟩ := hl
    exact ⟨xy, ⟨yv, yc, yv.trans_l vr⟩, hx, cv, vr, hc, hr⟩
  case _ a x b y c _ =>
    have ⟨_, _, yv, _, cv⟩ := lv; have ⟨ax, ⟨xy, xb, _⟩, ha, by_, yc, hb, hc⟩ := hl
    exact ⟨⟨xy, xy.trans_r ax, by_⟩, ⟨yv, yc, yv.trans_l vr⟩, ⟨ax, xb, ha, hb⟩, cv, vr, hc, hr⟩
  case _ => exact ⟨lv, vr, hl, hr⟩

@[simp] theorem balance1_All {l : RBNode α} {v : α} {r : RBNode α} :
    (balance1 l v r).All p ↔ p v ∧ l.All p ∧ r.All p := by
  unfold balance1; split <;> simp [and_assoc, and_left_comm]

/-- The second half of Okasaki's `balance`, concerning red-red sequences in the right child. -/
@[inline] def balance2 : RBNode α → α → RBNode α → RBNode α
  | a, x, node red (node red b y c) z d
  | a, x, node red b y (node red c z d) => node red (node black a x b) y (node black c z d)
  | a, x, b                             => node black a x b

/-- The `balance2` function preserves the ordering invariants. -/
protected theorem Ordered.balance2 {l : RBNode α} {v : α} {r : RBNode α}
    (lv : l.All (cmpLt cmp · v)) (vr : r.All (cmpLt cmp v ·))
    (hl : l.Ordered cmp) (hr : r.Ordered cmp) : (balance2 l v r).Ordered cmp := by
  unfold balance2; split
  case _ b y c z d =>
    have ⟨_, ⟨vy, vb, _⟩, _⟩ := vr; have ⟨⟨yz, _, cz⟩, zd, ⟨by_, yc, hy, hz⟩, hd⟩ := hr
    refine' ⟨⟨vy, vy.trans_r lv, by_⟩, ⟨yz, yc, yz.trans_l zd⟩, ⟨lv, vb, hl, hy⟩, cz, zd, hz, hd⟩
  case _ a x b y c _ =>
    have ⟨vx, va, _⟩ := vr; have ⟨ax, xy, ha, hy⟩ := hr
    exact ⟨⟨vx, vx.trans_r lv, ax⟩, xy, ⟨lv, va, hl, ha⟩, hy⟩
  case _ => exact ⟨lv, vr, hl, hr⟩

@[simp] theorem balance2_All {l : RBNode α} {v : α} {r : RBNode α} :
    (balance2 l v r).All p ↔ p v ∧ l.All p ∧ r.All p := by
  unfold balance2; split <;> simp [and_assoc, and_left_comm]

/-- An auxiliary function to test if the root is red. -/
def isRed : RBNode α → Bool
  | node red .. => true
  | _           => false

/-- An auxiliary function to test if the root is black (and non-nil). -/
def isBlack : RBNode α → Bool
  | node black .. => true
  | _             => false

/-- Change the color of the root to `black`. -/
def setBlack : RBNode α → RBNode α
  | nil          => nil
  | node _ l v r => node black l v r

protected theorem Ordered.setBlack {t : RBNode α} : (setBlack t).Ordered cmp ↔ t.Ordered cmp := by
  unfold setBlack; split <;> simp [Ordered]

protected theorem Balanced.setBlack : t.Balanced c n → ∃ n', (setBlack t).Balanced black n'
  | .nil => ⟨_, .nil⟩
  | .black hl hr | .red hl hr => ⟨_, hl.black hr⟩

section Insert

/--
The core of the `insert` function. This adds an element `x` to a balanced red-black tree.
Importantly, the result of callign `ins` is not a proper red-black tree,
because it has a broken balance invariant.
(See `InsBalanced` for the balance invariant of `ins`.)
The `insert` function does the final fixup needed to restore the invariant.
-/
@[specialize] def ins (cmp : α → α → Ordering) (x : α) : RBNode α → RBNode α
  | nil => node red nil x nil
  | node red a y b =>
    match cmp x y with
    | Ordering.lt => node red (ins cmp x a) y b
    | Ordering.gt => node red a y (ins cmp x b)
    | Ordering.eq => node red a x b
  | node black a y b =>
    match cmp x y with
    | Ordering.lt => balance1 (ins cmp x a) y b
    | Ordering.gt => balance2 a y (ins cmp x b)
    | Ordering.eq => node black a x b

protected theorem All.ins {x : α} {t : RBNode α}
  (h₁ : p x) (h₂ : t.All p) : (ins cmp x t).All p := by
  induction t <;> unfold ins <;> simp [*] <;> split <;>
    cases ‹_=_› <;> split <;> simp at h₂ <;> simp [*]

/-- The `ins` function preserves the ordering invariants. -/
protected theorem Ordered.ins : ∀ {t : RBNode α}, t.Ordered cmp → (ins cmp x t).Ordered cmp
  | nil, _ => ⟨⟨⟩, ⟨⟩, ⟨⟩, ⟨⟩⟩
  | node red a y b, ⟨ay, yb, ha, hb⟩ => by
    unfold ins; split
    case _ h => exact ⟨ay.ins ⟨h⟩, yb, ha.ins, hb⟩
    case _ h => exact ⟨ay, yb.ins ⟨LawfulCmp.cmp_eq_gt.1 h⟩, ha, hb.ins⟩
    case _ h => exact (⟨
      ay.imp fun ⟨h'⟩ => ⟨(TransCmp.cmp_congr_right h).trans h'⟩,
      yb.imp fun ⟨h'⟩ => ⟨(TransCmp.cmp_congr_left h).trans h'⟩, ha, hb⟩)
  | node black a y b, ⟨ay, yb, ha, hb⟩ => by
    unfold ins; split
    case _ h => exact ha.ins.balance1 (ay.ins ⟨h⟩) yb hb
    case _ h => exact ha.balance2 ay (yb.ins ⟨LawfulCmp.cmp_eq_gt.1 h⟩) hb.ins
    case _ h => exact (⟨
      ay.imp fun ⟨h'⟩ => ⟨(TransCmp.cmp_congr_right h).trans h'⟩,
      yb.imp fun ⟨h'⟩ => ⟨(TransCmp.cmp_congr_left h).trans h'⟩, ha, hb⟩)

/--
`insert cmp t v` inserts element `v` into the tree, using the provided comparator
`cmp` to put it in the right place and automatically rebalancing the tree as necessary.
-/
@[specialize] def insert (cmp : α → α → Ordering) (t : RBNode α) (v : α) : RBNode α :=
  bif isRed t then (ins cmp v t).setBlack else ins cmp v t

/-- The `insert` function preserves the ordering invariants. -/
protected theorem Ordered.insert (h : t.Ordered cmp) : (insert cmp t v).Ordered cmp := by
  unfold RBNode.insert cond; split <;> simp [Ordered.setBlack, h.ins (x := v)]

/--
The red-red invariant is a weakening of the red-black balance invariant which allows
the root to be red with red children, but does not allow any other violations.
-/
inductive RedRed : RBNode α → Nat → Prop where
  /-- A balanced tree has the red-red invariant. -/
  | balanced : Balanced t c n → RedRed t n
  /-- A red node with balanced red children has the red-red invariant. -/
  | redred : Balanced a c₁ n → Balanced b c₂ n → RedRed (node red a x b) n

/-- The `balance1` function repairs the balance invariant when the first argument is red-red. -/
protected theorem RedRed.balance1 {l : RBNode α} {v : α} {r : RBNode α}
    (hl : l.RedRed n) (hr : r.Balanced c n) : ∃ c, (balance1 l v r).Balanced c (n + 1) := by
  unfold balance1; split
  case _ a x b y c => match hl with
    | .redred (.red ha hb) hc => exact ⟨_, .red (.black ha hb) (.black hc hr)⟩
  case _ a x b y c _ => match hl with
    | .redred ha (.red hb hc) => exact ⟨_, .red (.black ha hb) (.black hc hr)⟩
  case _ H1 H2 => match hl with
    | .balanced hl => exact ⟨_, .black hl hr⟩
    | .redred (c₁ := black) (c₂ := black) ha hb => exact ⟨_, .black (.red ha hb) hr⟩
    | .redred (c₁ := red) (.red ..) _ => cases H1 _ _ _ _ _ rfl
    | .redred (c₂ := red) _ (.red ..) => cases H2 _ _ _ _ _ rfl

/-- The `balance2` function repairs the balance invariant when the first argument is red-red. -/
protected theorem RedRed.balance2 {l : RBNode α} {v : α} {r : RBNode α}
    (hl : l.Balanced c n) (hr : r.RedRed n) : ∃ c, (balance2 l v r).Balanced c (n + 1) := by
  unfold balance2; split
  case _ a x b y c => match hr with
    | .redred (.red ha hb) hc => exact ⟨_, .red (.black hl ha) (.black hb hc)⟩
  case _ a x b y c _ => match hr with
    | .redred ha (.red hb hc) => exact ⟨_, .red (.black hl ha) (.black hb hc)⟩
  case _ H1 H2 => match hr with
    | .balanced hr => exact ⟨_, .black hl hr⟩
    | .redred (c₁ := black) (c₂ := black) ha hb => exact ⟨_, .black hl (.red ha hb)⟩
    | .redred (c₁ := red) (.red ..) _ => cases H1 _ _ _ _ _ rfl
    | .redred (c₂ := red) _ (.red ..) => cases H2 _ _ _ _ _ rfl

/--
The balance invariant of the `ins` function.
`InsBalanced t₀ t n` is a property that should hold of `t` when inserting an element into `t₀`.
`n` is the black-height of `t₀`, and also of `t` (because `ins` does not change the black-height).
The result of inserting into the tree either yields a balanced tree,
or a tree which is almost balanced except that it has a red-red violation at the root.
-/
inductive InsBalanced : RBNode α → RBNode α → Nat → Prop where
  /-- A balanced tree is `ins`-balanced. -/
  | balanced : Balanced t c n → InsBalanced t₀ t n
  /-- The case where `t` has the form `red (red a b) c` violates the balance invariant,
  but it is otherwise valid (`a, b, c` are all balanced and black).
  Additionally, this case can only occur if `t₀` was red to begin with. -/
  | redL : Balanced a black n → Balanced b black n → Balanced c black n →
    InsBalanced (node red a₀ v₀ b₀) (node red (node red a x b) y c) n
  /-- The case where `t` has the form `red a (red b c)` violates the balance invariant,
  but it is otherwise valid (`a, b, c` are all balanced and black).
  Additionally, this case can only occur if `t₀` was red to begin with. -/
  | redR : Balanced a black n → Balanced b black n → Balanced c black n →
    InsBalanced (node red a₀ v₀ b₀) (node red a x (node red b y c)) n

protected theorem InsBalanced.redred {t₀ t : RBNode α} : t₀.InsBalanced t n → t.RedRed n
  | .balanced h => .balanced h
  | .redL ha hb hc => .redred (.red ha hb) hc
  | .redR ha hb hc => .redred ha (.red hb hc)

/-- The `ins` function is `ins`-balanced if the input is balanced. -/
protected theorem Balanced.ins (cmp v) {t : RBNode α}
    (h : t.Balanced c n) : t.InsBalanced (ins cmp v t) n := by
  induction h with
  | nil => exact .balanced (.red .nil .nil)
  | @red a n b x hl hr ihl ihr =>
    simp [ins]; split
    · match ins cmp v a, ihl with
      | _, .balanced .nil => exact .balanced (.red .nil hr)
      | _, .balanced (.red ha hb) => exact .redL ha hb hr
      | _, .balanced (.black ha hb) => exact .balanced (.red (.black ha hb) hr)
    · match ins cmp v b, ihr with
      | _, .balanced .nil => exact .balanced (.red hl .nil)
      | _, .balanced (.red ha hb) => exact .redR hl ha hb
      | _, .balanced (.black ha hb) => exact .balanced (.red hl (.black ha hb))
    · exact .balanced (.red hl hr)
  | @black a ca n b cb x hl hr ihl ihr =>
    simp [ins]; split
    · let ⟨c, h⟩ := ihl.redred.balance1 (v := x) hr; exact .balanced h
    · let ⟨c, h⟩ := ihr.redred.balance2 (v := x) hl; exact .balanced h
    · exact .balanced (.black hl hr)

/--
The `insert` function is balanced if the input is balanced.
(We lose track of both the color and the black-height of the result,
so this is only suitable for use on the root of the tree.)
-/
theorem Balanced.insert {t : RBNode α} (h : t.Balanced c n) :
    ∃ c' n', (insert cmp t v).Balanced c' n' := by
  unfold insert cond; match ins cmp v t, h.ins cmp v with
  | _, .balanced h => split; {exact ⟨_, h.setBlack⟩}; {exact ⟨_, _, h⟩}
  | _, .redL ha hb hc => simp [isRed, setBlack]; exact ⟨_, _, .black (.red ha hb) hc⟩
  | _, .redR ha hb hc => simp [isRed, setBlack]; exact ⟨_, _, .black ha (.red hb hc)⟩

end Insert

/-- The property of a cut function `cut` which ensures it can be used to find elements. -/
class IsCut (cmp : α → α → Ordering) (cut : α → Ordering) : Prop where
  /-- The set `{x | cut x = .lt}` is downward-closed. -/
  lt_trans : cmpLt cmp x y → cut x = .lt → cut y = .lt
  /-- The set `{x | cut x = .gt}` is upward-closed. -/
  gt_trans : cmpLt cmp x y → cut y = .gt → cut x = .gt

/-- A "representable cut" is one generated by `cmp a` for some `a`. This is always a valid cut. -/
instance (cmp) [TransCmp cmp] (a : α) : IsCut cmp (cmp a) where
  lt_trans h₁ h₂ := TransCmp.lt_trans h₂ h₁.1
  gt_trans h₁ h₂ := TransCmp.gt_trans h₂ (LawfulCmp.cmp_eq_gt.2 h₁.1)

/-- Okasaki's full `balance` function. This is a combination of `balance1` and `balance2`. -/
def balance (a : RBNode α) (v : α) (d : RBNode α) : RBNode α :=
  match a with
  | node red (node red a x b) y c
  | node red a x (node red b y c) => node red (node black a x b) y (node black c v d)
  | a => balance2 a v d

/-- The `balance` function preserves the ordering invariants. -/
protected theorem Ordered.balance {l : RBNode α} {v : α} {r : RBNode α}
    (lv : l.All (cmpLt cmp · v)) (vr : r.All (cmpLt cmp v ·))
    (hl : l.Ordered cmp) (hr : r.Ordered cmp) : (balance l v r).Ordered cmp := by
  have := hl.balance1 lv vr hr; revert this
  unfold balance1 balance; split <;> simp [*]
  · intro; exact hl.balance2 lv vr hr

/-- Recolor the root of the tree to `red` if possible. -/
def setRed : RBNode α → RBNode α
  | node _ a v b => node red a v b
  | nil          => nil

protected theorem Ordered.setRed {t : RBNode α} : (setRed t).Ordered cmp ↔ t.Ordered cmp := by
  unfold setRed; split <;> simp [Ordered]

/-- Rebalancing a tree which has shrunk on the left. -/
def balLeft (l : RBNode α) (v : α) (r : RBNode α) : RBNode α :=
  match l with
  | node red a x b                    => node red (node black a x b) v r
  | l => match r with
    | node black a y b                => balance2 l v (node red a y b)
    | node red (node black a y b) z c => node red (node black l v a) y (balance2 b z (setRed c))
    | r                               => node red l v r -- unreachable

/-- Rebalancing a tree which has shrunk on the right. -/
def balRight (l : RBNode α) (v : α) (r : RBNode α) : RBNode α :=
  match r with
  | node red b y c                    => node red l v (node black b y c)
  | r => match l with
    | node black a x b                => balance1 (node red a x b) v r
    | node red a x (node black b y c) => node red (balance1 (setRed a) x b) y (node black c v r)
    | l                               => node red l v r -- unreachable

/-- The number of nodes in the tree. -/
@[simp] def size : RBNode α → Nat
  | nil => 0
  | node _ x _ y => x.size + y.size + 1

/--
The invariant of the `append` function. The main theorem is `Balanced.append`:
if `l.Balanced c₁ n` and `r.Balanced c₂ n` then `(l.append r).AppendProp c₁ c₂ n`.
-/
inductive AppendProp : RBColor → RBColor → RBNode α → Nat → Prop
  /-- It is always okay to make a balanced tree of black-height `n`. -/
  | balanced : Balanced t c n → AppendProp c₁ c₂ t n
  /-- It is okay to make a red-red tree of black-height `n`
  as long as `c₁` and `c₂` are not both black. -/
  | redder : (c₁ = black → c₂ ≠ black) →
    Balanced x cx n → Balanced y cy n → AppendProp c₁ c₂ (node red x v y) n

/-- The result of the append function is a red-red tree. -/
theorem AppendProp.redred : AppendProp c₁ c₂ t n → t.RedRed n
  | .balanced h => .balanced h
  | .redder _ ha hb => .redred ha hb

/-- The result of the append function is a red-black tree when both inputs are black. -/
theorem AppendProp.of_black : AppendProp black black t n → ∃ c, Balanced t c n
  | .balanced h => ⟨_, h⟩
  | .redder h _ _ => nomatch h rfl rfl

/-- Concatenate two trees with the same black-height. -/
def append : RBNode α → RBNode α → RBNode α
  | nil, x | x, nil => x
  | node red a x b, node red c y d =>
    match append b c with
    | node red b' z c' => node red (node red a x b') z (node red c' y d)
    | bc               => node red a x (node red bc y d)
  | node black a x b, node black c y d =>
    match append b c with
    | node red b' z c' => node red (node black a x b') z (node black c' y d)
    | bc               => balLeft a x (node black bc y d)
  | a@(node black ..), node red b x c => node red (append a b) x c
  | node red a x b, c@(node black ..) => node red a x (append b c)
termination_by _ x y => x.size + y.size

protected theorem Balanced.append {l r : RBNode α}
    (hl : l.Balanced c₁ n) (hr : r.Balanced c₂ n) : (l.append r).AppendProp c₁ c₂ n := by
  unfold append; split
  case _ x => exact .balanced hr
  case _ x _ => exact .balanced hl
  case _ a x b c y d =>
    have .red ha hb := hl; have .red hc hd := hr
    have ⟨_, IH⟩ := (hb.append hc).of_black; split
    case _ b' z c' e =>
      have .red hb' hc' := e ▸ IH
      exact .redder (fun.) (.red ha hb') (.red hc' hd)
    case _ bcc _ H =>
      match bcc, append b c, IH, H with
      | black, _, IH, _ => refine' .redder (fun.) ha (.red IH hd)
      | red, _, .red .., H => cases H _ _ _ rfl
  case _ a x b c y d =>
    have .black ha hb := hl; have .black hc hd := hr
    have IH := hb.append hc; split
    case _ b' z c' e => match e ▸ IH with
      | .balanced (.red hb' hc') | .redder _ hb' hc' =>
        exact .balanced (.red (.black ha hb') (.black hc' hd))
    case _ cc dc _ H =>
      match append b c, IH, H with
      | bc, .balanced hbc, _ =>
        unfold balLeft; split
        case _ a' x b' =>
          have .red ha' hb' := ha
          exact .balanced (.red (.black ha' hb') (.black hbc hd))
        case _ _ x b =>
          exact have ⟨c, h⟩ := RedRed.balance2 ha (.redred hbc hd); .balanced h
      | _, .redder .., H => cases H _ _ _ rfl
  case _ a x b c y d =>
    have .red hc hd := hr; have IH := hl.append hc
    have .black ha hb := hl; have ⟨c, IH⟩ := IH.of_black
    exact .redder (fun.) IH hd
  case _ a x b c y d =>
    have .red ha hb := hl; have IH := hb.append hr
    have .black hc hd := hr; have ⟨c, IH⟩ := IH.of_black
    exact .redder (fun.) ha IH
termination_by _ x y _ _ => x.size + y.size

/-! ## erase -/

/-- The invariant of the `del` function. -/
inductive DelProp : RBNode α → RBNode α → Nat → Prop
  /-- If the input tree is red or nil, then the result of deletion is a balanced tree with
  some color and the same black-height. -/
  | balanced : t₀.isBlack = false → Balanced t c n → DelProp t₀ t n
  /-- If the input tree is black, then the result of deletion is a red-red tree with
  black-height lowered by 1. -/
  | redred : t₀.isBlack = true → RedRed t n → DelProp t₀ t (n + 1)

/--
The core of the `erase` function. The tree returned from this function has a broken invariant,
which is restored in `erase`.
-/
@[specialize] def del (cut : α → Ordering) : RBNode α → RBNode α
  | nil          => nil
  | node _ a y b =>
    match cut y with
    | .lt => bif a.isBlack then balLeft (del cut a) y b else node red (del cut a) y b
    | .gt => bif b.isBlack then balRight a y (del cut b) else node red a y (del cut b)
    | .eq => append a b

/--
The `erase cut t` function removes an element from the tree `t`.
The `cut` function is used to locate an element in the tree:
it returns `.gt` if we go too high and `.lt` if we go too low;
if it returns `.eq` we will remove the element.
(The function `cmp k` for some key `k` is a valid cut function, but we can also use cuts that
are not of this form as long as they are suitably monotonic.)
-/
@[specialize] def erase (cut : α → Ordering) (t : RBNode α) : RBNode α := (del cut t).setBlack

section Membership

/-- Finds an element in the tree satisfying the `cut` function. -/
@[specialize] def find? (cut : α → Ordering) : RBNode α → Option α
  | nil => none
  | node _ a y b =>
    match cut y with
    | .lt => find? cut a
    | .gt => find? cut b
    | .eq => some y

/-- `lowerBound? cut` retrieves the largest entry smaller than or equal to `cut`, if it exists. -/
@[specialize] def lowerBound? (cut : α → Ordering) : RBNode α → Option α → Option α
  | nil,          lb => lb
  | node _ a y b, lb =>
    match cut y with
    | .lt => lowerBound? cut a lb
    | .gt => lowerBound? cut b (some y)
    | .eq => some y

end Membership

/-- Map a function on every value in the tree. This can break the order invariant  -/
@[specialize] def map (f : α → β) : RBNode α → RBNode β
  | nil => nil
  | node c l v r => node c (l.map f) (f v) (r.map f)

/-- Converts the tree into an array in increasing sorted order. -/
def toArray (n : RBNode α) : Array α := n.foldl (init := #[]) (·.push ·)

instance : EmptyCollection (RBNode α) := ⟨nil⟩

end RBNode

open RBNode

/--
An `RBTree` is a self-balancing binary search tree.
The `cmp` function is the comparator that will be used for performing searches;
it should satisfy the requirements of `TransCmp` for it to have sensible behavior.
-/
def RBTree (α : Type u) (cmp : α → α → Ordering) : Type u :=
  {t : RBNode α // t.Ordered cmp ∧ ∃ c n, t.Balanced c n}

/-- `O(1)`. Construct a new empty tree. -/
@[inline] def mkRBTree (α : Type u) (cmp : α → α → Ordering) : RBTree α cmp :=
  ⟨.nil, ⟨⟩, _, _, .nil⟩

namespace RBTree

/-- `O(1)`. Construct a new empty tree. -/
@[inline] def empty : RBTree α cmp := mkRBTree ..

instance (α : Type u) (cmp : α → α → Ordering) : EmptyCollection (RBTree α cmp) := ⟨empty⟩

instance (α : Type u) (cmp : α → α → Ordering) : Inhabited (RBTree α cmp) := ⟨∅⟩

/-- `O(1)`. Construct a new tree with one element `v`. -/
@[inline] def single (v : α) : RBTree α cmp :=
  ⟨.node .red .nil v .nil, ⟨⟨⟩, ⟨⟩, ⟨⟩, ⟨⟩⟩, _, _, .red .nil .nil⟩

/-- `O(n)`. Fold a function on the values from left to right (in increasing order). -/
@[inline] def foldl (f : σ → α → σ) (init : σ) (t : RBTree α cmp) : σ := t.1.foldl f init

/-- `O(n)`. Fold a function on the values from right to left (in decreasing order). -/
@[inline] def foldr (f : α → σ → σ) (init : σ) (t : RBTree α cmp) : σ := t.1.foldr f init

/-- `O(n)`. Fold a monadic function on the values from left to right (in increasing order). -/
@[inline] def foldlM [Monad m] (f : σ → α → m σ) (init : σ) (t : RBTree α cmp) : m σ :=
  t.1.foldlM f init

/-- `O(n)`. Run monadic function `f` on each element of the tree (in increasing order). -/
@[inline] def forM [Monad m] (f : α → m PUnit) (t : RBTree α cmp) : m PUnit := t.1.forM f

instance : ForIn m (RBTree α cmp) α where
  forIn t init f := t.1.forIn init f

/-- `O(1)`. Is the tree empty? -/
@[inline] def isEmpty : RBTree α cmp → Bool
  | ⟨nil, _⟩ => true
  | _        => false

/-- `O(n)`. Convert the tree to a list in ascending order. -/
@[specialize] def toList (t : RBTree α cmp) : List α := t.1.foldr (·::·) []

/-- `O(log n)`. Returns the entry `a` such that `a ≤ k` for all keys in the RBTree. -/
@[inline] protected def min (t : RBTree α cmp) : Option α := t.1.min

/-- `O(log n)`. Returns the entry `a` such that `a ≥ k` for all keys in the RBTree. -/
@[inline] protected def max (t : RBTree α cmp) : Option α := t.1.max

instance [Repr α] : Repr (RBTree α cmp) where
  reprPrec m prec := Repr.addAppParen ("Std.rbmapOf " ++ repr m.toList) prec

/-- `O(log n)`. Insert element `v` into the tree. -/
@[inline] def insert (t : RBTree α cmp) (v : α) : RBTree α cmp :=
  ⟨t.1.insert cmp v, let ⟨o, _, _, h⟩ := t.2; ⟨o.insert, h.insert⟩⟩

-- TODO
-- @[inline] def erase : RBTree α cmp → α → RBTree α cmp
--   | ⟨t, w⟩, k => ⟨t.erase cmp k, WellFormed.eraseWff w rfl⟩

/-- `O(log n)`. Find an element in the tree using a cut function. -/
@[inline] def findP? (t : RBTree α cmp) (cut : α → Ordering) : Option α := t.1.find? cut

/-- `O(log n)`. Returns an element in the tree equivalent to `x` if one exists. -/
@[inline] def find? (t : RBTree α cmp) (x : α) : Option α := t.1.find? (cmp x)

/-- `O(log n)`. Find an element in the tree, or return a default value `v₀`. -/
@[inline] def findPD (t : RBTree α cmp) (cut : α → Ordering) (v₀ : α) : α := (t.findP? cut).getD v₀

/--
`O(log n)`. `lowerBoundP cut` retrieves the largest entry comparing `lt` or `eq` under `cut`,
if it exists.
-/
@[inline] def lowerBoundP? (t : RBTree α cmp) (cut : α → Ordering) : Option α :=
  t.1.lowerBound? cut none

/--
`O(log n)`. `lowerBound? k` retrieves the largest entry smaller than or equal to `k`,
if it exists.
-/
@[inline] def lowerBound? (t : RBTree α cmp) (k : α) : Option α := t.1.lowerBound? (cmp k) none

/-- `O(log n)`. Returns true if the given cut returns `eq` for something in the RBTree. -/
@[inline] def containsP (t : RBTree α cmp) (cut : α → Ordering) : Bool := (t.findP? cut).isSome

/-- `O(log n)`. Returns true if the given key `a` is in the RBTree. -/
@[inline] def contains (t : RBTree α cmp) (a : α) : Bool := (t.find? a).isSome

/-- `O(n log n)`. Build a tree from an unsorted list by inserting them one at a time. -/
@[inline] def ofList (l : List α) (cmp : α → α → Ordering) : RBTree α cmp :=
  l.foldl (fun r p => r.insert p) (mkRBTree α cmp)

/-- `O(n log n)`. Build a tree from an unsorted array by inserting them one at a time. -/
@[inline] def ofArray (l : Array α) (cmp : α → α → Ordering) : RBTree α cmp :=
  l.foldl (fun r p => r.insert p) (mkRBTree α cmp)

/-- `O(n)`. Returns true if the given predicate is true for all items in the RBTree. -/
@[inline] def all (t : RBTree α cmp) (p : α → Bool) : Bool := t.1.all p

/-- `O(n)`. Returns true if the given predicate is true for any item in the RBTree. -/
@[inline] def any (t : RBTree α cmp) (p : α → Bool) : Bool := t.1.any p

/-- `O(n)`. The number of items in the RBTree. -/
def size (m : RBTree α cmp) : Nat := m.1.size

/-- `O(log n)`. Returns the minimum element of the tree, or panics if the tree is empty. -/
@[inline] def min! [Inhabited α] (t : RBTree α cmp) : α := t.min.getD (panic! "tree is empty")

/-- `O(log n)`. Returns the maximum element of the tree, or panics if the tree is empty. -/
@[inline] def max! [Inhabited α] (t : RBTree α cmp) : α := t.max.getD (panic! "tree is empty")

/--
`O(log n)`. Attempts to find the value with key `k : α` in `t` and panics if there is no such key.
-/
@[inline] def findP! [Inhabited α] (t : RBTree α cmp) (cut : α → Ordering) : α :=
  (t.findP? cut).getD (panic! "key is not in the tree")

/--
`O(log n)`. Attempts to find the value with key `k : α` in `t` and panics if there is no such key.
-/
@[inline] def find! [Inhabited α] (t : RBTree α cmp) (k : α) : α :=
  (t.find? k).getD (panic! "key is not in the tree")

/--
`O(n₂ * log (n₁ + n₂))`. Merges the maps `t₁` and `t₂`. If equal keys exist in both,
then use `mergeFn a₁ a₂` to produce the new merged value.
-/
def mergeBy (mergeFn : α → α → α) (t₁ t₂ : RBTree α cmp) : RBTree α cmp :=
  t₂.foldl (init := t₁) fun t₁ a₂ =>
    t₁.insert <| match t₁.find? a₂ with | some a₁ => mergeFn a₁ a₂ | none => a₂

/--
`O(n₁ * log (n₁ + n₂))`. Intersects the maps `t₁` and `t₂`
using `mergeFn a b` to produce the new value.
-/
def intersectBy (cmp : α → β → Ordering) (mergeFn : α → β → γ)
    (t₁ : RBTree α cmpα) (t₂ : RBTree β cmpβ) : RBTree γ cmpγ :=
  t₁.foldl (init := ∅) fun acc a =>
      match t₂.findP? (cmp a) with
      | some b => acc.insert <| mergeFn a b
      | none => acc

end RBTree

/- TODO(Leo): define dRBMap -/

/--
An `RBTree` is a self-balancing binary search tree, used to store a key-value map.
The `cmp` function is the comparator that will be used for performing searches;
it should satisfy the requirements of `TransCmp` for it to have sensible behavior.
-/
def RBMap (α : Type u) (β : Type v) (cmp : α → α → Ordering) : Type (max u v) :=
  RBTree (α × β) (fun a b => cmp a.1 b.1)

/-- `O(1)`. Construct a new empty map. -/
@[inline] def mkRBMap (α : Type u) (β : Type v) (cmp : α → α → Ordering) : RBMap α β cmp :=
  mkRBTree ..

/-- `O(1)`. Construct a new empty map. -/
@[inline] def RBMap.empty {α : Type u} {β : Type v} {cmp : α → α → Ordering} : RBMap α β cmp :=
  mkRBMap ..

instance (α : Type u) (β : Type v) (cmp : α → α → Ordering) : EmptyCollection (RBMap α β cmp) :=
  ⟨RBMap.empty⟩

instance (α : Type u) (β : Type v) (cmp : α → α → Ordering) : Inhabited (RBMap α β cmp) := ⟨∅⟩

/-- `O(1)`. Construct a new tree with one key-value pair `k, v`. -/
@[inline] def single (k : α) (v : β) : RBMap α β cmp := RBTree.single (k, v)

namespace RBMap
variable {α : Type u} {β : Type v} {σ : Type w} {cmp : α → α → Ordering}

/-- `O(n)`. Fold a function on the values from left to right (in increasing order). -/
@[inline] def foldl (f : σ → α → β → σ) : (init : σ) → RBMap α β cmp → σ
  | b, ⟨t, _⟩ => t.foldl (fun s (a, b) => f s a b) b

/-- `O(n)`. Fold a function on the values from right to left (in decreasing order). -/
@[inline] def foldr (f : α → β → σ → σ) : (init : σ) → RBMap α β cmp → σ
  | b, ⟨t, _⟩ => t.foldr (fun (a, b) s => f a b s) b

/-- `O(n)`. Fold a monadic function on the values from left to right (in increasing order). -/
@[inline] def foldlM [Monad m] (f : σ → α → β → m σ) : (init : σ) → RBMap α β cmp → m σ
  | b, ⟨t, _⟩ => t.foldlM (fun s (a, b) => f s a b) b

/-- `O(n)`. Run monadic function `f` on each element of the tree (in increasing order). -/
@[inline] def forM [Monad m] (f : α → β → m PUnit) (t : RBMap α β cmp) : m PUnit :=
  t.foldlM (fun _ k v => f k v) ⟨⟩

instance : ForIn m (RBMap α β cmp) (α × β) where
  forIn t init f := t.val.forIn init f

/-- `O(1)`. Is the tree empty? -/
@[inline] def isEmpty : RBMap α β cmp → Bool := RBTree.isEmpty

/-- `O(n)`. Convert the tree to a list in ascending order. -/
@[inline] def toList : RBMap α β cmp → List (α × β) := RBTree.toList

/-- `O(log n)`. Returns the key-value pair `(a,b)` such that `a ≤ k` for all keys in the RBMap. -/
@[inline] protected def min : RBMap α β cmp → Option (α × β) := RBTree.min

/-- `O(log n)`. Returns the key-value pair `(a,b)` such that `a ≥ k` for all keys in the RBMap. -/
@[inline] protected def max : RBMap α β cmp → Option (α × β) := RBTree.max

instance [Repr α] [Repr β] : Repr (RBMap α β cmp) where
  reprPrec m prec := Repr.addAppParen ("RBMap.fromList " ++ repr m.toList) prec

/-- `O(log n)`. Insert key-value pair `(k,v)` into the tree. -/
@[inline] def insert (t : RBMap α β cmp) (k : α) (v : β) : RBMap α β cmp := RBTree.insert t (k, v)

-- TODO
-- @[inline] def erase : RBMap α β cmp → α → RBMap α β cmp
--   | ⟨t, w⟩, k => ⟨t.erase cmp k, WellFormed.eraseWff w rfl⟩

/-- `O(n log n)`. Build a tree from an unsorted list by inserting them one at a time. -/
@[inline] def ofList (l : List (α × β)) (cmp : α → α → Ordering) : RBMap α β cmp :=
  RBTree.ofList l _

/-- `O(n log n)`. Build a tree from an unsorted array by inserting them one at a time. -/
@[inline] def ofArray (l : Array (α × β)) (cmp : α → α → Ordering) : RBMap α β cmp :=
  RBTree.ofArray l _

/-- `O(log n)`. Find an entry in the tree with key equal to `k`. -/
@[inline] def findEntry? (t : RBMap α β cmp) (k : α) : Option (α × β) := t.findP? (cmp k ·.1)

/-- `O(log n)`. Find the value corresponding to key `k`. -/
@[inline] def find? (t : RBMap α β cmp) (k : α) : Option β := t.findEntry? k |>.map (·.2)

/-- `O(log n)`. Find the value corresponding to key `k`, or return `v₀` if it is not in the map. -/
@[inline] def findD (t : RBMap α β cmp) (k : α) (v₀ : β) : β := (t.find? k).getD v₀

/--
`O(log n)`. `lowerBound? k` retrieves the key-value pair of the largest key
smaller than or equal to `k`, if it exists.
-/
@[inline] def lowerBound? (t : RBMap α β cmp) (k : α) : Option (α × β) :=
   RBTree.lowerBoundP? t (cmp k ·.1)

/-- `O(log n)`. Returns true if the given key `a` is in the RBMap. -/
@[inline] def contains (t : RBMap α β cmp) (a : α) : Bool := (t.findEntry? a).isSome

/-- `O(n)`. Returns true if the given predicate is true for all items in the RBMap. -/
@[inline] def all (t : RBMap α β cmp) (p : α → β → Bool) : Bool := RBTree.all t fun (a, b) => p a b

/-- `O(n)`. Returns true if the given predicate is true for any item in the RBMap. -/
@[inline] def any (t : RBMap α β cmp) (p : α → β → Bool) : Bool := RBTree.all t fun (a, b) => p a b

/-- `O(n)`. The number of items in the RBMap. -/
def size : RBMap α β cmp → Nat := RBTree.size

/-- `O(log n)`. Returns the minimum element of the map, or panics if the map is empty. -/
@[inline] def min! [Inhabited α] [Inhabited β] : RBMap α β cmp → α × β := RBTree.min!

/-- `O(log n)`. Returns the maximum element of the map, or panics if the map is empty. -/
@[inline] def max! [Inhabited α] [Inhabited β] : RBMap α β cmp → α × β := RBTree.max!

/-- Attempts to find the value with key `k : α` in `t` and panics if there is no such key. -/
@[inline] def find! [Inhabited β] (t : RBMap α β cmp) (k : α) : β :=
  (t.find? k).getD (panic! "key is not in the map")

/--
`O(n₂ * log (n₁ + n₂))`. Merges the maps `t₁` and `t₂`, if a key `a : α` exists in both,
then use `mergeFn a b₁ b₂` to produce the new merged value.
-/
def mergeBy (mergeFn : α → β → β → β) (t₁ t₂ : RBMap α β cmp) : RBMap α β cmp :=
  RBTree.mergeBy (fun (_, b₁) (a, b₂) => (a, mergeFn a b₁ b₂)) t₁ t₂

/--
`O(n₁ * log (n₁ + n₂))`. Intersects the maps `t₁` and `t₂`
using `mergeFn a b` to produce the new value.
-/
def intersectBy (mergeFn : α → β → γ → δ)
    (t₁ : RBMap α β cmp) (t₂ : RBMap α γ cmp) : RBMap α δ cmp :=
  RBTree.intersectBy (cmp ·.1 ·.1) (fun (a, b₁) (_, b₂) => (a, mergeFn a b₁ b₂)) t₁ t₂

end RBMap
end Std.New
open Std.New

@[inheritDoc RBMap.ofList]
abbrev List.toRBMap (l : List (α × β)) (cmp : α → α → Ordering) : RBMap α β cmp :=
  RBMap.ofList l cmp

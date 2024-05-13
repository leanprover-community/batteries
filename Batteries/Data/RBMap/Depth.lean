/-
Copyright (c) 2022 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Batteries.Data.RBMap.WF

/-!
# RBNode depth bounds
-/

namespace Batteries.RBNode
open RBColor

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

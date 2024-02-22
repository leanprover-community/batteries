/-
Copyright (c) 2022 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/

/-! ## Ordering -/

@[simp] theorem Ordering.swap_swap {o : Ordering} : o.swap.swap = o := by cases o <;> rfl

@[simp] theorem Ordering.swap_inj {o₁ o₂ : Ordering} : o₁.swap = o₂.swap ↔ o₁ = o₂ :=
  ⟨fun h => by simpa using congrArg swap h, congrArg _⟩

namespace Std

/-- `TotalBLE le` asserts that `le` has a total order, that is, `le a b ∨ le b a`. -/
class TotalBLE (le : α → α → Bool) : Prop where
  /-- `le` is total: either `le a b` or `le b a`. -/
  total : le a b ∨ le b a

/-- `OrientedCmp cmp` asserts that `cmp` is determined by the relation `cmp x y = .lt`. -/
class OrientedCmp (cmp : α → α → Ordering) : Prop where
  /-- The comparator operation is symmetric, in the sense that if `cmp x y` equals `.lt` then
  `cmp y x = .gt` and vice versa. -/
  symm (x y) : (cmp x y).swap = cmp y x

namespace OrientedCmp

theorem cmp_eq_gt [OrientedCmp cmp] : cmp x y = .gt ↔ cmp y x = .lt := by
  rw [← Ordering.swap_inj, symm]; exact .rfl

theorem cmp_eq_eq_symm [OrientedCmp cmp] : cmp x y = .eq ↔ cmp y x = .eq := by
  rw [← Ordering.swap_inj, symm]; exact .rfl

theorem cmp_refl [OrientedCmp cmp] : cmp x x = .eq :=
  match e : cmp x x with
  | .lt => nomatch e.symm.trans (cmp_eq_gt.2 e)
  | .eq => rfl
  | .gt => nomatch (cmp_eq_gt.1 e).symm.trans e

end OrientedCmp

/-- `TransCmp cmp` asserts that `cmp` induces a transitive relation. -/
class TransCmp (cmp : α → α → Ordering) extends OrientedCmp cmp : Prop where
  /-- The comparator operation is transitive. -/
  le_trans : cmp x y ≠ .gt → cmp y z ≠ .gt → cmp x z ≠ .gt

namespace TransCmp
variable [TransCmp cmp]
open OrientedCmp Decidable

theorem ge_trans (h₁ : cmp x y ≠ .lt) (h₂ : cmp y z ≠ .lt) : cmp x z ≠ .lt := by
  have := @TransCmp.le_trans _ cmp _ z y x
  simp [cmp_eq_gt] at *; exact this h₂ h₁

theorem lt_asymm (h : cmp x y = .lt) : cmp y x ≠ .lt :=
  fun h' => nomatch h.symm.trans (cmp_eq_gt.2 h')

theorem gt_asymm (h : cmp x y = .gt) : cmp y x ≠ .gt :=
  mt cmp_eq_gt.1 <| lt_asymm <| cmp_eq_gt.1 h

theorem le_lt_trans (h₁ : cmp x y ≠ .gt) (h₂ : cmp y z = .lt) : cmp x z = .lt :=
  byContradiction fun h₃ => ge_trans (mt cmp_eq_gt.2 h₁) h₃ h₂

theorem lt_le_trans (h₁ : cmp x y = .lt) (h₂ : cmp y z ≠ .gt) : cmp x z = .lt :=
  byContradiction fun h₃ => ge_trans h₃ (mt cmp_eq_gt.2 h₂) h₁

theorem lt_trans (h₁ : cmp x y = .lt) (h₂ : cmp y z = .lt) : cmp x z = .lt :=
  le_lt_trans (gt_asymm <| cmp_eq_gt.2 h₁) h₂

theorem gt_trans (h₁ : cmp x y = .gt) (h₂ : cmp y z = .gt) : cmp x z = .gt := by
  rw [cmp_eq_gt] at h₁ h₂ ⊢; exact lt_trans h₂ h₁

theorem cmp_congr_left (xy : cmp x y = .eq) : cmp x z = cmp y z :=
  match yz : cmp y z with
  | .lt => byContradiction (ge_trans (nomatch ·.symm.trans (cmp_eq_eq_symm.1 xy)) · yz)
  | .gt => byContradiction (le_trans (nomatch ·.symm.trans (cmp_eq_eq_symm.1 xy)) · yz)
  | .eq => match xz : cmp x z with
    | .lt => nomatch ge_trans (nomatch ·.symm.trans xy) (nomatch ·.symm.trans yz) xz
    | .gt => nomatch le_trans (nomatch ·.symm.trans xy) (nomatch ·.symm.trans yz) xz
    | .eq => rfl

theorem cmp_congr_left' (xy : cmp x y = .eq) : cmp x = cmp y :=
  funext fun _ => cmp_congr_left xy

theorem cmp_congr_right [TransCmp cmp] (yz : cmp y z = .eq) : cmp x y = cmp x z := by
  rw [← Ordering.swap_inj, symm, symm, cmp_congr_left yz]

end TransCmp

end Std

namespace Ordering

open Std

/-- Pull back a comparator by a function `f`, by applying the comparator to both arguments. -/
@[inline] def byKey (f : α → β) (cmp : β → β → Ordering) (a b : α) : Ordering := cmp (f a) (f b)

instance (f : α → β) (cmp : β → β → Ordering) [OrientedCmp cmp] : OrientedCmp (byKey f cmp) where
  symm a b := OrientedCmp.symm (f a) (f b)

instance (f : α → β) (cmp : β → β → Ordering) [TransCmp cmp] : TransCmp (byKey f cmp) where
  le_trans h₁ h₂ := TransCmp.le_trans (α := β) h₁ h₂

instance (f : α → β) (cmp : β → β → Ordering) [TransCmp cmp] : TransCmp (byKey f cmp) where
  le_trans h₁ h₂ := TransCmp.le_trans (α := β) h₁ h₂

end Ordering

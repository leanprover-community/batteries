/-
Copyright (c) 2022 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Std.Tactic.Simpa

/-! ## Ordering -/

deriving instance DecidableEq for Ordering

/-- Swaps less and greater ordering results -/
def Ordering.swap : Ordering → Ordering
  | .lt => .gt
  | .eq => .eq
  | .gt => .lt

@[simp] theorem Ordering.swap_swap {o : Ordering} : o.swap.swap = o := by cases o <;> rfl

@[simp] theorem Ordering.swap_inj {o₁ o₂ : Ordering} : o₁.swap = o₂.swap ↔ o₁ = o₂ :=
  ⟨fun h => by simpa using congrArg swap h, congrArg _⟩

/--
If `o₁` and `o₂` are `Ordering`, then `o₁.then o₂` returns `o₁` unless it is `.eq`,
in which case it returns `o₂`. Additionally, it has "short-circuiting" semantics similar to
boolean `x && y`: if `o₁` is not `.eq` then the expression for `o₂` is not evaluated.
This is a useful primitive for constructing lexicographic comparator functions:
```
structure Person where
  name : String
  age : Nat

instance : Ord Person where
  compare a b := (compare a.name b.name).then (compare b.age a.age)
```
This example will sort people first by name (in ascending order) and will sort people with
the same name by age (in descending order). (If all fields are sorted ascending and in the same
order as they are listed in the structure, you can also use `deriving Ord` on the structure
definition for the same effect.)
-/
@[macro_inline] def Ordering.then : Ordering → Ordering → Ordering
  | .eq, f => f
  | o, _ => o

namespace Std

/-- `TotalBLE le` asserts that `le` has a total order, that is, `le a b ∨ le b a`. -/
class TotalBLE (le : α → α → Bool) : Prop where
  /-- `le` is total: either `le a b` or `le b a`. -/
  total : le a b ∨ le b a

/-- `OrientedCmp cmp` asserts that `cmp` is determined by the relation `cmp x y = .lt`. -/
class OrientedCmp (cmp : α → α → Ordering) : Prop where
  /-- The comparator operation is swap-symmetric. -/
  cmp_swap_symm (x y) : (cmp x y).swap = cmp y x

/-- `OrientedOrd α` asserts that `compare` is determined by the relation `compare x y = .lt`. -/
class abbrev OrientedOrd (α) [self : Ord α] := OrientedCmp self.compare

namespace OrientedCmp
variable {cmp : α → α → Ordering} [OrientedCmp cmp]

theorem cmp_gt_lt_symm : cmp x y = .gt ↔ cmp y x = .lt := by
  rw [← Ordering.swap_inj, cmp_swap_symm]; exact .rfl

theorem cmp_eq_eq_symm : cmp x y = .eq ↔ cmp y x = .eq := by
  rw [← Ordering.swap_inj, cmp_swap_symm]; exact .rfl

theorem cmp_eq_refl : cmp x x = .eq :=
  match e : cmp x x with
  | .lt => nomatch e.symm.trans (cmp_gt_lt_symm.2 e)
  | .eq => rfl
  | .gt => nomatch (cmp_gt_lt_symm.1 e).symm.trans e

theorem cmp_lt_irrefl : cmp x x ≠ .lt := fun h => Ordering.noConfusion (cmp_eq_refl (cmp:=cmp) ▸ h)

theorem cmp_gt_irrefl : cmp x x ≠ .gt := fun h => Ordering.noConfusion (cmp_eq_refl (cmp:=cmp) ▸ h)

theorem cmp_le_total : cmp x y ≠ .gt ∨ cmp y x ≠ .gt :=
  match h : cmp x y with
  | .lt => .inl Ordering.noConfusion
  | .gt => .inr fun h' => Ordering.noConfusion (cmp_gt_lt_symm.1 h ▸ h')
  | .eq => .inl Ordering.noConfusion

theorem cmp_ge_total : cmp x y ≠ .lt ∨ cmp y x ≠ .lt :=
  match h : cmp x y with
  | .lt => .inr fun h' => Ordering.noConfusion (cmp_gt_lt_symm.2 h ▸ h')
  | .gt => .inl Ordering.noConfusion
  | .eq => .inl Ordering.noConfusion

end OrientedCmp

/-- `TransCmp cmp` asserts that `cmp` induces a transitive relation. -/
class TransCmp (cmp : α → α → Ordering) extends OrientedCmp cmp : Prop where
  /-- The comparator operation is transitive. -/
  cmp_le_trans : cmp x y ≠ .gt → cmp y z ≠ .gt → cmp x z ≠ .gt

/-- `TransOrd α` asserts that `compare` induces a transitive relation. -/
class abbrev TransOrd (α) [self : Ord α] := TransCmp self.compare

namespace TransCmp
variable {cmp : α → α → Ordering} [TransCmp cmp]
open OrientedCmp Decidable

theorem cmp_ge_trans {x y z} (h₁ : cmp x y ≠ .lt) (h₂ : cmp y z ≠ .lt) : cmp x z ≠ .lt := by
  have := @cmp_le_trans _ cmp _ z y x
  simp [cmp_gt_lt_symm] at *; exact this h₂ h₁

theorem cmp_lt_asymm (h : cmp x y = .lt) : cmp y x ≠ .lt :=
  fun h' => nomatch h.symm.trans (cmp_gt_lt_symm.2 h')

theorem cmp_gt_asymm (h : cmp x y = .gt) : cmp y x ≠ .gt :=
  mt cmp_gt_lt_symm.1 <| cmp_lt_asymm <| cmp_gt_lt_symm.1 h

theorem cmp_le_lt_trans (h₁ : cmp x y ≠ .gt) (h₂ : cmp y z = .lt) : cmp x z = .lt :=
  byContradiction fun h₃ => cmp_ge_trans (mt cmp_gt_lt_symm.2 h₁) h₃ h₂

theorem cmp_lt_le_trans (h₁ : cmp x y = .lt) (h₂ : cmp y z ≠ .gt) : cmp x z = .lt :=
  byContradiction fun h₃ => cmp_ge_trans h₃ (mt cmp_gt_lt_symm.2 h₂) h₁

theorem cmp_lt_trans (h₁ : cmp x y = .lt) (h₂ : cmp y z = .lt) : cmp x z = .lt :=
  cmp_le_lt_trans (cmp_gt_asymm <| cmp_gt_lt_symm.2 h₁) h₂

theorem cmp_ge_gt_trans (h₁ : cmp x y ≠ .lt) (h₂ : cmp y z = .gt) : cmp x z = .gt :=
  byContradiction fun h₃ => cmp_le_trans (mt cmp_gt_lt_symm.1 h₁) h₃ h₂

theorem cmp_gt_ge_trans (h₁ : cmp x y = .gt) (h₂ : cmp y z ≠ .lt) : cmp x z = .gt :=
  byContradiction fun h₃ => cmp_le_trans h₃ (mt cmp_gt_lt_symm.1 h₂) h₁

theorem cmp_gt_trans (h₁ : cmp x y = .gt) (h₂ : cmp y z = .gt) : cmp x z = .gt := by
  rw [cmp_gt_lt_symm] at h₁ h₂ ⊢; exact cmp_lt_trans h₂ h₁

theorem cmp_congr_left (xy : cmp x y = .eq) : cmp x z = cmp y z :=
  match yz : cmp y z with
  | .lt => byContradiction (cmp_ge_trans (nomatch ·.symm.trans (cmp_eq_eq_symm.1 xy)) · yz)
  | .gt => byContradiction (cmp_le_trans (nomatch ·.symm.trans (cmp_eq_eq_symm.1 xy)) · yz)
  | .eq => match xz : cmp x z with
    | .lt => nomatch cmp_ge_trans (nomatch ·.symm.trans xy) (nomatch ·.symm.trans yz) xz
    | .gt => nomatch cmp_le_trans (nomatch ·.symm.trans xy) (nomatch ·.symm.trans yz) xz
    | .eq => rfl

theorem cmp_congr_right (yz : cmp y z = .eq) : cmp x y = cmp x z := by
  rw [← Ordering.swap_inj, cmp_swap_symm, cmp_swap_symm, cmp_congr_left yz]

end TransCmp

/-- `LinearCmp cmp` asserts that `cmp` induces a linear ordering. -/
class LinearCmp (cmp : α → α → Ordering) extends TransCmp cmp : Prop where
  /-- The comparator equality is strict. -/
  cmp_eq_strict : cmp x y = .eq → x = y

/-- `LinearOrd α` asserts that `compare` induces a linear ordering. -/
class abbrev LinearOrd (α) [self : Ord α] := LinearCmp self.compare

namespace LinearCmp
variable {cmp : α → α → Ordering} [LinearCmp cmp]
open OrientedCmp TransCmp

theorem cmp_eq_iff_eq : cmp x y = .eq ↔ x = y :=
  ⟨cmp_eq_strict, fun | rfl => cmp_eq_refl⟩

theorem cmp_antisymm (h₁ : cmp x y ≠ .lt) (h₂ : cmp x y ≠ .gt) : x = y :=
  match h : cmp x y with
  | .lt => absurd h h₁
  | .gt => absurd h h₂
  | .eq => cmp_eq_strict h

theorem cmp_le_antisymm (h₁ : cmp x y ≠ .lt) (h₂ : cmp y x ≠ .lt) : x = y :=
  cmp_antisymm h₁ (mt cmp_gt_lt_symm.1 h₂)

theorem cmp_ge_antisymm (h₁ : cmp x y ≠ .gt) (h₂ : cmp y x ≠ .gt) : x = y :=
  cmp_antisymm (mt cmp_gt_lt_symm.2 h₂) h₁

theorem cmp_lt_connex (hne : x ≠ y) : cmp x y = .lt ∨ cmp y x = .lt :=
  match h : cmp x y with
  | .lt => .inl rfl
  | .gt => .inr (cmp_gt_lt_symm.1 h)
  | .eq => absurd (cmp_eq_strict h) hne

theorem cmp_gt_connex (hne : x ≠ y) : cmp x y = .gt ∨ cmp y x = .gt :=
  match h : cmp x y with
  | .lt => .inr (cmp_gt_lt_symm.2 h)
  | .gt => .inl rfl
  | .eq => absurd (cmp_eq_strict h) hne

end LinearCmp

/-- Pull back a comparator by a function `f`, by applying the comparator to both arguments. -/
@[inline] def byKey (f : α → β) (cmp : β → β → Ordering) (a b : α) : Ordering := cmp (f a) (f b)

instance (f : α → β) (cmp : β → β → Ordering) [OrientedCmp cmp] : OrientedCmp (byKey f cmp) where
  cmp_swap_symm a b := OrientedCmp.cmp_swap_symm (f a) (f b)

instance (f : α → β) (cmp : β → β → Ordering) [TransCmp cmp] : TransCmp (byKey f cmp) where
  cmp_le_trans h₁ h₂ := TransCmp.cmp_le_trans (α := β) h₁ h₂

instance (f : α → β) (cmp : β → β → Ordering) [TransCmp cmp] : TransCmp (byKey f cmp) where
  cmp_le_trans h₁ h₂ := TransCmp.cmp_le_trans (α := β) h₁ h₂

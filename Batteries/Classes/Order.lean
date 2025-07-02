/-
Copyright (c) 2022 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Batteries.Tactic.Basic
import Batteries.Tactic.SeqFocus
import Std.Classes.Ord

theorem lexOrd_def [Ord α] [Ord β] :
    (lexOrd : Ord (α × β)).compare = compareLex (compareOn (·.1)) (compareOn (·.2)) := rfl

/-- Pull back a comparator by a function `f`, by applying the comparator to both arguments. -/
@[inline] def Ordering.byKey (f : α → β) (cmp : β → β → Ordering) (a b : α) : Ordering :=
  cmp (f a) (f b)

namespace Batteries

/-- `TotalBLE le` asserts that `le` has a total order, that is, `le a b ∨ le b a`. -/
class TotalBLE (le : α → α → Bool) : Prop where
  /-- `le` is total: either `le a b` or `le b a`. -/
  total : le a b ∨ le b a

theorem compareOfLessAndEq_eq_lt {x y : α} [LT α] [Decidable (x < y)] [DecidableEq α] :
    compareOfLessAndEq x y = .lt ↔ x < y := by
  simp [compareOfLessAndEq]
  split <;> simp

end Batteries

/-! Batteries features not in core Std -/

namespace Std
open Batteries (compareOfLessAndEq_eq_lt)

namespace OrientedCmp
variable {cmp : α → α → Ordering} [OrientedCmp cmp]

theorem le_iff_ge : cmp x y ≠ .gt ↔ cmp y x ≠ .lt :=
  not_congr OrientedCmp.gt_iff_lt

end OrientedCmp

namespace TransCmp
variable {cmp : α → α → Ordering} [TransCmp cmp]

theorem le_trans : cmp x y ≠ .gt → cmp y z ≠ .gt → cmp x z ≠ .gt := by
  simp only [ne_eq, ← Ordering.isLE_iff_ne_gt]; exact isLE_trans

theorem lt_of_lt_of_le : cmp x y = .lt → cmp y z ≠ .gt → cmp x z = .lt := by
  simp only [ne_eq, ← Ordering.isLE_iff_ne_gt]; exact lt_of_lt_of_isLE

theorem lt_of_le_of_lt : cmp x y ≠ .gt → cmp y z = .lt → cmp x z = .lt := by
  simp only [ne_eq, ← Ordering.isLE_iff_ne_gt]; exact lt_of_isLE_of_lt

theorem ge_trans : cmp x y ≠ .lt → cmp y z ≠ .lt → cmp x z ≠ .lt := by
  simp only [ne_eq, ← Ordering.isGE_iff_ne_lt]; exact isGE_trans

theorem gt_of_gt_of_ge : cmp x y = .gt → cmp y z ≠ .lt → cmp x z = .gt := by
  simp only [ne_eq, ← Ordering.isGE_iff_ne_lt]; exact gt_of_gt_of_isGE

theorem gt_of_ge_of_gt : cmp x y ≠ .lt → cmp y z = .gt → cmp x z = .gt := by
  simp only [ne_eq, ← Ordering.isGE_iff_ne_lt]; exact gt_of_isGE_of_gt

end TransCmp

/-- `LawfulLTCmp cmp` asserts that `cmp x y = .lt` and `x < y` coincide. -/
class LawfulLTCmp [LT α] (cmp : α → α → Ordering) : Prop extends OrientedCmp cmp where
  /-- `cmp x y = .lt` holds iff `x < y` is true. -/
  eq_lt_iff_lt : cmp x y = .lt ↔ x < y

theorem LawfulLTCmp.eq_gt_iff_gt [LT α] [LawfulLTCmp (α := α) cmp] :
    cmp x y = .gt ↔ y < x := by rw [OrientedCmp.gt_iff_lt, eq_lt_iff_lt]

/-- `LawfulLECmp cmp` asserts that `(cmp x y).isLE` and `x ≤ y` coincide. -/
class LawfulLECmp [LE α] (cmp : α → α → Ordering) : Prop extends OrientedCmp cmp where
  /-- `cmp x y ≠ .gt` holds iff `x ≤ y` is true. -/
  isLE_iff_le : (cmp x y).isLE ↔ x ≤ y

theorem LawfulLECmp.isGE_iff_ge [LE α] [LawfulLECmp (α := α) cmp] :
    (cmp x y).isGE ↔ y ≤ x := by rw [← Ordering.isLE_swap, ← OrientedCmp.eq_swap, isLE_iff_le]

theorem LawfulLECmp.ne_gt_iff_le [LE α] [LawfulLECmp (α := α) cmp] :
    cmp x y ≠ .gt ↔ x ≤ y := by rw [← isLE_iff_le (cmp := cmp), Ordering.isLE_iff_ne_gt]

theorem LawfulLECmp.ne_lt_iff_ge [LE α] [LawfulLECmp (α := α) cmp] :
    cmp x y ≠ .lt ↔ y ≤ x := by rw [← isGE_iff_ge (cmp := cmp), Ordering.isGE_iff_ne_lt]

/-- `LawfulBCmp cmp` asserts that the `LE`, `LT`, `BEq` are all coherent with each other
and with `cmp`, describing a strict weak order (a linear order except for antisymmetry). -/
class LawfulBCmp [LE α] [LT α] [BEq α] (cmp : α → α → Ordering) : Prop extends
  TransCmp cmp, LawfulBEqCmp cmp, LawfulLTCmp cmp, LawfulLECmp cmp

/-- `LawfulBCmp cmp` asserts that the `LE`, `LT`, `Eq` are all coherent with each other
and with `cmp`, describing a linear order. -/
class LawfulCmp [LE α] [LT α] (cmp : α → α → Ordering) : Prop extends
  TransCmp cmp, LawfulEqCmp cmp, LawfulLTCmp cmp, LawfulLECmp cmp

/-- Class for types where the ordering function is compatible with the `LT`. -/
abbrev LawfulLTOrd (α) [LT α] [Ord α] := LawfulLTCmp (α := α) compare

/-- Class for types where the ordering function is compatible with the `LE`. -/
abbrev LawfulLEOrd (α) [LE α] [Ord α] := LawfulLECmp (α := α) compare

/-- Class for types where the ordering function is compatible with the `LE`, `LT` and `BEq`. -/
abbrev LawfulBOrd (α) [LE α] [LT α] [BEq α] [Ord α] := LawfulBCmp (α := α) compare

/-- Class for types where the ordering function is compatible with the `LE`, `LT` and `Eq`. -/
abbrev LawfulOrd (α) [LE α] [LT α] [Ord α] := LawfulCmp (α := α) compare

instance [inst : Std.OrientedCmp cmp] : Std.OrientedCmp (flip cmp) where
  eq_swap := inst.eq_swap

instance [inst : Std.TransCmp cmp] : Std.TransCmp (flip cmp) where
  isLE_trans h1 h2 := inst.isLE_trans h2 h1

instance (f : α → β) (cmp : β → β → Ordering) [Std.OrientedCmp cmp] :
    Std.OrientedCmp (Ordering.byKey f cmp) where
  eq_swap {a b} := Std.OrientedCmp.eq_swap (a := f a) (b := f b)

instance (f : α → β) (cmp : β → β → Ordering) [Std.TransCmp cmp] :
    Std.TransCmp (Ordering.byKey f cmp) where
  isLE_trans h₁ h₂ := Std.TransCmp.isLE_trans (α := β) h₁ h₂

instance [inst₁ : OrientedCmp cmp₁] [inst₂ : OrientedCmp cmp₂] :
    OrientedCmp (compareLex cmp₁ cmp₂) := inferInstance

instance [inst₁ : TransCmp cmp₁] [inst₂ : TransCmp cmp₂] :
    TransCmp (compareLex cmp₁ cmp₂) := inferInstance

instance [Ord β] [OrientedOrd β] (f : α → β) : OrientedCmp (compareOn f) := inferInstance

instance [Ord β] [TransOrd β] (f : α → β) : TransCmp (compareOn f) := inferInstance

theorem OrientedOrd.instOn [ord : Ord β] [OrientedOrd β] (f : α → β) : @OrientedOrd _ (ord.on f) :=
  inferInstanceAs (@OrientedCmp _ (compareOn f))

theorem TransOrd.instOn [ord : Ord β] [TransOrd β] (f : α → β) : @TransOrd _ (ord.on f) :=
  inferInstanceAs (@TransCmp _ (compareOn f))

theorem OrientedOrd.instOrdLex' (ord₁ ord₂ : Ord α) [@OrientedOrd _ ord₁] [@OrientedOrd _ ord₂] :
    @OrientedOrd _ (ord₁.lex' ord₂) :=
  inferInstanceAs (OrientedCmp (compareLex ord₁.compare ord₂.compare))

theorem TransOrd.instOrdLex' (ord₁ ord₂ : Ord α) [@TransOrd _ ord₁] [@TransOrd _ ord₂] :
    @TransOrd _ (ord₁.lex' ord₂) :=
  inferInstanceAs (TransCmp (compareLex ord₁.compare ord₂.compare))

theorem LawfulLTCmp.eq_compareOfLessAndEq
    [LT α] [DecidableEq α] [LawfulEqCmp cmp] [LawfulLTCmp cmp]
    (x y : α) [Decidable (x < y)] : cmp x y = compareOfLessAndEq x y := by
  simp only [compareOfLessAndEq]
  split <;> rename_i h1 <;> [skip; split <;> rename_i h2]
  · exact LawfulLTCmp.eq_lt_iff_lt.2 h1
  · exact LawfulEqCmp.compare_eq_iff_eq.2 h2
  · cases e : cmp x y
    · cases h1 (LawfulLTCmp.eq_lt_iff_lt.1 e)
    · cases h2 (LawfulEqCmp.compare_eq_iff_eq.1 e)
    · rfl

theorem ReflCmp.compareOfLessAndEq_of_lt_irrefl [LT α] [DecidableLT α] [DecidableEq α]
    (lt_irrefl : ∀ x : α, ¬ x < x) :
    ReflCmp (α := α) (compareOfLessAndEq · ·) where
  compare_self {x} := by simp [compareOfLessAndEq, if_neg (lt_irrefl x)]

theorem LawfulBEqCmp.compareOfLessAndEq_of_lt_irrefl
    [LT α] [DecidableLT α] [DecidableEq α] [BEq α] [LawfulBEq α]
    (lt_irrefl : ∀ x : α, ¬x < x) :
    LawfulBEqCmp (α := α) (compareOfLessAndEq · ·) where
  compare_eq_iff_beq {x y} := by
    simp [compareOfLessAndEq]
    split <;> [skip; split] <;> simp [*]
    rintro rfl; exact lt_irrefl _ ‹_›

-- redundant? See `compareOfLessAndEq_of_lt_trans_of_lt_iff` in core
theorem TransCmp.compareOfLessAndEq_of_lt_irrefl_of_lt_trans_of_lt_antisymm
    [LT α] [DecidableLT α] [DecidableEq α]
    (lt_irrefl : ∀ x : α, ¬x < x)
    (lt_trans : ∀ {x y z : α}, x < y → y < z → x < z)
    (lt_antisymm : ∀ {x y : α}, ¬x < y → ¬y < x → x = y) :
    TransCmp (α := α) (compareOfLessAndEq · ·) :=
  TransOrd.compareOfLessAndEq_of_lt_trans_of_lt_iff lt_trans <| by
    intros
    constructor
    · intro h₁
      constructor
      · intro h₂
        apply lt_irrefl
        exact lt_trans h₁ h₂
      · intro | rfl => exact lt_irrefl _ h₁
    · intro ⟨h₁, h₂⟩
      by_contra h₃
      apply h₂
      exact lt_antisymm h₃ h₁

-- redundant? See `compareOfLessAndEq_of_antisymm_of_trans_of_total_of_not_le` in core
theorem TransCmp.compareOfLessAndEq_of_lt_irrefl_of_lt_trans_of_not_lt_of_le_antisymm
    [LT α] [LE α] [DecidableLT α] [DecidableEq α]
    (lt_irrefl : ∀ x : α, ¬x < x)
    (lt_trans : ∀ {x y z : α}, x < y → y < z → x < z)
    (not_lt : ∀ {x y : α}, ¬x < y → y ≤ x)
    (le_antisymm : ∀ {x y : α}, x ≤ y → y ≤ x → x = y) :
    TransCmp (α := α) (compareOfLessAndEq · ·) :=
  .compareOfLessAndEq_of_lt_irrefl_of_lt_trans_of_lt_antisymm
    lt_irrefl lt_trans fun xy yx => le_antisymm (not_lt yx) (not_lt xy)

-- make redundant?
theorem LawfulLTCmp.compareOfLessAndEq_of_lt_irrefl_of_lt_trans_of_lt_antisymm
    [LT α] [DecidableLT α] [DecidableEq α]
    (lt_irrefl : ∀ x : α, ¬x < x)
    (lt_trans : ∀ {x y z : α}, x < y → y < z → x < z)
    (lt_antisymm : ∀ {x y : α}, ¬x < y → ¬y < x → x = y) :
    LawfulLTCmp (α := α) (compareOfLessAndEq · ·) :=
  { TransCmp.compareOfLessAndEq_of_lt_irrefl_of_lt_trans_of_lt_antisymm
      lt_irrefl lt_trans lt_antisymm with
    eq_lt_iff_lt := Batteries.compareOfLessAndEq_eq_lt }

-- make redundant?
theorem LawfulLTCmp.compareOfLessAndEq_of_lt_irrefl_of_lt_trans_of_not_lt_of_le_antisymm
    [LT α] [DecidableLT α] [DecidableEq α] [LE α]
    (lt_irrefl : ∀ x : α, ¬x < x)
    (lt_trans : ∀ {x y z : α}, x < y → y < z → x < z)
    (not_lt : ∀ {x y : α}, ¬x < y → y ≤ x)
    (le_antisymm : ∀ {x y : α}, x ≤ y → y ≤ x → x = y) :
    LawfulLTCmp (α := α) (compareOfLessAndEq · ·) :=
  { TransCmp.compareOfLessAndEq_of_lt_irrefl_of_lt_trans_of_not_lt_of_le_antisymm
      lt_irrefl lt_trans not_lt le_antisymm with
    eq_lt_iff_lt := Batteries.compareOfLessAndEq_eq_lt }

-- make redundant?
theorem LawfulLECmp.compareOfLessAndEq_of_lt_irrefl_of_lt_trans_of_not_lt_of_le_antisymm
    [LT α] [DecidableLT α] [DecidableEq α] [LE α]
    (lt_irrefl : ∀ x : α, ¬x < x)
    (lt_trans : ∀ {x y z : α}, x < y → y < z → x < z)
    (not_lt : ∀ {x y : α}, ¬x < y ↔ y ≤ x)
    (le_antisymm : ∀ {x y : α}, x ≤ y → y ≤ x → x = y) :
    LawfulLECmp (α := α) (compareOfLessAndEq · ·) :=
  have := TransCmp.compareOfLessAndEq_of_lt_irrefl_of_lt_trans_of_not_lt_of_le_antisymm
      lt_irrefl lt_trans not_lt.1 le_antisymm
  { this with
    isLE_iff_le := by
      intro x y
      simp only [Ordering.isLE_iff_ne_gt, ← not_lt]
      apply not_congr
      rw [this.gt_iff_lt, Batteries.compareOfLessAndEq_eq_lt] }

theorem LawfulCmp.compareOfLessAndEq_of_lt_irrefl_of_lt_trans_of_not_lt_of_le_antisymm
    [LT α] [LE α] [DecidableLT α] [DecidableLE α] [DecidableEq α]
    (lt_irrefl : ∀ x : α, ¬x < x)
    (lt_trans : ∀ {x y z : α}, x < y → y < z → x < z)
    (not_lt : ∀ {x y : α}, ¬x < y ↔ y ≤ x)
    (le_antisymm : ∀ {x y : α}, x ≤ y → y ≤ x → x = y) :
    LawfulCmp (α := α) (compareOfLessAndEq · ·) :=
    have instT := TransCmp.compareOfLessAndEq_of_lt_irrefl_of_lt_trans_of_not_lt_of_le_antisymm
      lt_irrefl lt_trans not_lt.1 le_antisymm
    have instLT := LawfulLTCmp.compareOfLessAndEq_of_lt_irrefl_of_lt_trans_of_not_lt_of_le_antisymm
      lt_irrefl lt_trans not_lt.1 le_antisymm
    have instLE := LawfulLECmp.compareOfLessAndEq_of_lt_irrefl_of_lt_trans_of_not_lt_of_le_antisymm
      lt_irrefl lt_trans not_lt le_antisymm
    have le_refl (x : α) : x ≤ x := by rw [← not_lt]; exact lt_irrefl _
    have not_le {x y : α} : ¬x ≤ y ↔ y < x := by simp [← not_lt]
    { instT, instLT, instLE with
      eq_of_compare {_  _}:= by rw [compareOfLessAndEq_eq_eq le_refl not_le]; exact id
    }

end Std

/-! Deprecated Batteries comparison classes -/

set_option linter.deprecated false

namespace Batteries

/-- `OrientedCmp cmp` asserts that `cmp` is determined by the relation `cmp x y = .lt`. -/
@[deprecated "Std.OrientedCmp" (since := "2025-07-01")]
class OrientedCmp (cmp : α → α → Ordering) : Prop where
  /-- The comparator operation is symmetric, in the sense that if `cmp x y` equals `.lt` then
  `cmp y x = .gt` and vice versa. -/
  symm (x y) : (cmp x y).swap = cmp y x

attribute [deprecated "Std.OrientedOrd.eq_swap" (since := "2025-07-01")] OrientedCmp.symm

namespace OrientedCmp

@[deprecated "Std.OrientedCmp.gt_iff_lt" (since := "2025-07-01")]
theorem cmp_eq_gt [OrientedCmp cmp] : cmp x y = .gt ↔ cmp y x = .lt := by
  rw [← Ordering.swap_inj, symm]; exact .rfl

@[deprecated "Std.OrientedCmp.le_iff_ge" (since := "2025-07-01")]
theorem cmp_ne_gt [OrientedCmp cmp] : cmp x y ≠ .gt ↔ cmp y x ≠ .lt := not_congr cmp_eq_gt

@[deprecated "Std.OrientedCmp.eq_comm" (since := "2025-07-01")]
theorem cmp_eq_eq_symm [OrientedCmp cmp] : cmp x y = .eq ↔ cmp y x = .eq := by
  rw [← Ordering.swap_inj, symm]; exact .rfl

@[deprecated "Std.ReflCmp.compare_self" (since := "2025-07-01")]
theorem cmp_refl [OrientedCmp cmp] : cmp x x = .eq :=
  match e : cmp x x with
  | .lt => nomatch e.symm.trans (cmp_eq_gt.2 e)
  | .eq => rfl
  | .gt => nomatch (cmp_eq_gt.1 e).symm.trans e

@[deprecated "Std.OrientedCmp.not_lt_of_lt"  (since := "2025-07-01")]
theorem lt_asymm [OrientedCmp cmp] (h : cmp x y = .lt) : cmp y x ≠ .lt :=
  fun h' => nomatch h.symm.trans (cmp_eq_gt.2 h')

@[deprecated "Std.OrientedCmp.not_gt_of_gt"  (since := "2025-07-01")]
theorem gt_asymm [OrientedCmp cmp] (h : cmp x y = .gt) : cmp y x ≠ .gt :=
  mt cmp_eq_gt.1 <| lt_asymm <| cmp_eq_gt.1 h

end OrientedCmp

/-- `TransCmp cmp` asserts that `cmp` induces a transitive relation. -/
@[deprecated "Std.TransCmp" (since := "2025-07-01")]
class TransCmp (cmp : α → α → Ordering) : Prop extends OrientedCmp cmp where
  /-- The comparator operation is transitive. -/
  le_trans : cmp x y ≠ .gt → cmp y z ≠ .gt → cmp x z ≠ .gt

attribute [deprecated "Std.TransCmp.le_trans" (since := "2025-07-01")] TransCmp.le_trans

namespace TransCmp
variable [TransCmp cmp]
open OrientedCmp Decidable

@[deprecated "Std.TransCmp.ge_trans" (since := "2025-07-01")]
theorem ge_trans (h₁ : cmp x y ≠ .lt) (h₂ : cmp y z ≠ .lt) : cmp x z ≠ .lt := by
  have := @TransCmp.le_trans _ cmp _ z y x
  simp [cmp_eq_gt] at *; exact this h₂ h₁

@[deprecated "Std.TransCmp.lt_of_le_of_lt" (since := "2025-07-01")]
theorem le_lt_trans (h₁ : cmp x y ≠ .gt) (h₂ : cmp y z = .lt) : cmp x z = .lt :=
  byContradiction fun h₃ => ge_trans (mt cmp_eq_gt.2 h₁) h₃ h₂

@[deprecated "Std.TransCmp.lt_of_lt_of_le" (since := "2025-07-01")]
theorem lt_le_trans (h₁ : cmp x y = .lt) (h₂ : cmp y z ≠ .gt) : cmp x z = .lt :=
  byContradiction fun h₃ => ge_trans h₃ (mt cmp_eq_gt.2 h₂) h₁

@[deprecated "Std.TransCmp.lt_trans" (since := "2025-07-01")]
theorem lt_trans (h₁ : cmp x y = .lt) (h₂ : cmp y z = .lt) : cmp x z = .lt :=
  le_lt_trans (gt_asymm <| cmp_eq_gt.2 h₁) h₂

@[deprecated "Std.TransCmp.gt_trans" (since := "2025-07-01")]
theorem gt_trans (h₁ : cmp x y = .gt) (h₂ : cmp y z = .gt) : cmp x z = .gt := by
  rw [cmp_eq_gt] at h₁ h₂ ⊢; exact lt_trans h₂ h₁

@[deprecated "Std.TransCmp.congr_left" (since := "2025-07-01")]
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

@[deprecated "Std.TransCmp.congr_right" (since := "2025-07-01")]
theorem cmp_congr_right (yz : cmp y z = .eq) : cmp x y = cmp x z := by
  rw [← Ordering.swap_inj, symm, symm, cmp_congr_left yz]

end TransCmp

instance [inst : OrientedCmp cmp] : OrientedCmp (flip cmp) where
  symm _ _ := inst.symm ..

instance [inst : TransCmp cmp] : TransCmp (flip cmp) where
  le_trans h1 h2 := inst.le_trans h2 h1

/-- `BEqCmp cmp` asserts that `cmp x y = .eq` and `x == y` coincide. -/
@[deprecated "Std.LawfulBEqCmp" (since := "2025-07-01")]
class BEqCmp [BEq α] (cmp : α → α → Ordering) : Prop where
  /-- `cmp x y = .eq` holds iff `x == y` is true. -/
  cmp_iff_beq : cmp x y = .eq ↔ x == y

attribute [deprecated "Std.TransCmp.compare_eq_iff_beq" (since := "2025-07-01")] BEqCmp.cmp_iff_beq

@[deprecated "Std.LawfulEqCmp.compare_eq_iff_eq" (since := "2025-07-01")]
theorem BEqCmp.cmp_iff_eq [BEq α] [LawfulBEq α] [BEqCmp (α := α) cmp] : cmp x y = .eq ↔ x = y := by
  simp [BEqCmp.cmp_iff_beq]

/-- `LTCmp cmp` asserts that `cmp x y = .lt` and `x < y` coincide. -/
@[deprecated "Std.LawfulLTCmp" (since := "2025-07-01")]
class LTCmp [LT α] (cmp : α → α → Ordering) : Prop extends OrientedCmp cmp where
  /-- `cmp x y = .lt` holds iff `x < y` is true. -/
  cmp_iff_lt : cmp x y = .lt ↔ x < y

attribute [deprecated "Std.LawfulLTCmp.eq_lt_iff_lt" (since := "2025-07-01")] LTCmp.cmp_iff_lt

@[deprecated "Std.LawfulLTCmp.eq_gt_iff_gt" (since := "2025-07-01")]
theorem LTCmp.cmp_iff_gt [LT α] [LTCmp (α := α) cmp] : cmp x y = .gt ↔ y < x := by
  rw [OrientedCmp.cmp_eq_gt, LTCmp.cmp_iff_lt]

/-- `LECmp cmp` asserts that `cmp x y ≠ .gt` and `x ≤ y` coincide. -/
@[deprecated "Std.LawfulLECmp" (since := "2025-07-01")]
class LECmp [LE α] (cmp : α → α → Ordering) : Prop extends OrientedCmp cmp where
  /-- `cmp x y ≠ .gt` holds iff `x ≤ y` is true. -/
  cmp_iff_le : cmp x y ≠ .gt ↔ x ≤ y

attribute [deprecated "Std.LawfulLECmp.ne_gt_iff_le" (since := "2025-07-01")] LECmp.cmp_iff_le

@[deprecated "Std.LawfulLECmp.ne_lt_iff_ge" (since := "2025-07-01")]
theorem LECmp.cmp_iff_ge [LE α] [LECmp (α := α) cmp] : cmp x y ≠ .lt ↔ y ≤ x := by
  rw [← OrientedCmp.cmp_ne_gt, LECmp.cmp_iff_le]

/-- `LawfulCmp cmp` asserts that the `LE`, `LT`, `BEq` instances are all coherent with each other
and with `cmp`, describing a strict weak order (a linear order except for antisymmetry). -/
@[deprecated "Std.LawfulBCmp" (since := "2025-07-01")]
class LawfulCmp [LE α] [LT α] [BEq α] (cmp : α → α → Ordering) : Prop extends
  TransCmp cmp, BEqCmp cmp, LTCmp cmp, LECmp cmp

/-- `OrientedOrd α` asserts that the `Ord` instance satisfies `OrientedCmp`. -/
@[deprecated "Std.OrientedOrd" (since := "2025-07-01")]
abbrev OrientedOrd (α) [Ord α] := OrientedCmp (α := α) compare

/-- `TransOrd α` asserts that the `Ord` instance satisfies `TransCmp`. -/
@[deprecated "Std.TransOrd" (since := "2025-07-01")]
abbrev TransOrd (α) [Ord α] := TransCmp (α := α) compare

/-- `BEqOrd α` asserts that the `Ord` and `BEq` instances are coherent via `BEqCmp`. -/
@[deprecated "Std.LawfulBEqOrd" (since := "2025-07-01")]
abbrev BEqOrd (α) [BEq α] [Ord α] := BEqCmp (α := α) compare

/-- `LTOrd α` asserts that the `Ord` instance satisfies `LTCmp`. -/
@[deprecated "Std.LawfulLTOrd" (since := "2025-07-01")]
abbrev LTOrd (α) [LT α] [Ord α] := LTCmp (α := α) compare

/-- `LEOrd α` asserts that the `Ord` instance satisfies `LECmp`. -/
@[deprecated "Std.LawfulLEOrd" (since := "2025-07-01")]
abbrev LEOrd (α) [LE α] [Ord α] := LECmp (α := α) compare

/-- `LawfulOrd α` asserts that the `Ord` instance satisfies `LawfulCmp`. -/
@[deprecated "Std.LawfulBOrd" (since := "2025-07-01")]
abbrev LawfulOrd (α) [LE α] [LT α] [BEq α] [Ord α] := LawfulCmp (α := α) compare

@[deprecated "Std.TransCmp.compareOfLessAndEq_of_lt_irrefl_of_lt_trans_of_lt_antisymm"
  (since := "2025-07-01")]
protected theorem TransCmp.compareOfLessAndEq
    [LT α] [DecidableRel (LT.lt (α := α))] [DecidableEq α]
    (lt_irrefl : ∀ x : α, ¬x < x)
    (lt_trans : ∀ {x y z : α}, x < y → y < z → x < z)
    (lt_antisymm : ∀ {x y : α}, ¬x < y → ¬y < x → x = y) :
    TransCmp (α := α) (compareOfLessAndEq · ·) := by
  have : OrientedCmp (α := α) (compareOfLessAndEq · ·) := by
    refine { symm := fun x y => ?_ }
    simp [compareOfLessAndEq]; split <;> [rename_i xy; split <;> [subst y; rename_i xy ne]]
    · rw [if_neg, if_neg]; rfl
      · rintro rfl; exact lt_irrefl _ xy
      · exact fun yx => lt_irrefl _ (lt_trans xy yx)
    · rw [if_neg ‹_›, if_pos rfl]; rfl
    · split <;> [rfl; rename_i yx]
      cases ne (lt_antisymm xy yx)
  refine { this with le_trans := fun {x y z} yx zy => ?_ }
  rw [Ne, this.cmp_eq_gt, compareOfLessAndEq_eq_lt] at yx zy ⊢
  intro zx
  if xy : x < y then exact zy (lt_trans zx xy)
  else exact zy (lt_antisymm yx xy ▸ zx)

@[deprecated "Std.TransCmp.compareOfLessAndEq_of_lt_irrefl_of_lt_trans_of_not_lt_of_le_antisymm"
  (since := "2025-07-01")]
theorem TransCmp.compareOfLessAndEq_of_le
    [LT α] [LE α] [DecidableRel (LT.lt (α := α))] [DecidableEq α]
    (lt_irrefl : ∀ x : α, ¬x < x)
    (lt_trans : ∀ {x y z : α}, x < y → y < z → x < z)
    (not_lt : ∀ {x y : α}, ¬x < y → y ≤ x)
    (le_antisymm : ∀ {x y : α}, x ≤ y → y ≤ x → x = y) :
    TransCmp (α := α) (compareOfLessAndEq · ·) :=
  .compareOfLessAndEq lt_irrefl lt_trans fun xy yx => le_antisymm (not_lt yx) (not_lt xy)

@[deprecated "Std.LawfulBEqCmp.compareOfLessAndEq_of_lt_irrefl" (since := "2025-07-01")]
protected theorem BEqCmp.compareOfLessAndEq
    [LT α] [DecidableRel (LT.lt (α := α))] [DecidableEq α] [BEq α] [LawfulBEq α]
    (lt_irrefl : ∀ x : α, ¬x < x) :
    BEqCmp (α := α) (compareOfLessAndEq · ·) where
  cmp_iff_beq {x y} := by
    simp [compareOfLessAndEq]
    split <;> [skip; split] <;> simp [*]
    rintro rfl; exact lt_irrefl _ ‹_›

@[deprecated "Std.LawfulLTCmp.compareOfLessAndEq_of_lt_irrefl_of_lt_trans_of_lt_antisymm"
  (since := "2025-07-01")]
protected theorem LTCmp.compareOfLessAndEq
    [LT α] [DecidableRel (LT.lt (α := α))] [DecidableEq α]
    (lt_irrefl : ∀ x : α, ¬x < x)
    (lt_trans : ∀ {x y z : α}, x < y → y < z → x < z)
    (lt_antisymm : ∀ {x y : α}, ¬x < y → ¬y < x → x = y) :
    LTCmp (α := α) (compareOfLessAndEq · ·) :=
  { TransCmp.compareOfLessAndEq lt_irrefl lt_trans lt_antisymm with
    cmp_iff_lt := compareOfLessAndEq_eq_lt }

@[deprecated "Std.LawfulLTCmp.compareOfLessAndEq_of_lt_irrefl_of_lt_trans_of_not_lt_of_le_antisymm"
  (since := "2025-07-01")]
protected theorem LTCmp.compareOfLessAndEq_of_le
    [LT α] [DecidableRel (LT.lt (α := α))] [DecidableEq α] [LE α]
    (lt_irrefl : ∀ x : α, ¬x < x)
    (lt_trans : ∀ {x y z : α}, x < y → y < z → x < z)
    (not_lt : ∀ {x y : α}, ¬x < y → y ≤ x)
    (le_antisymm : ∀ {x y : α}, x ≤ y → y ≤ x → x = y) :
    LTCmp (α := α) (compareOfLessAndEq · ·) :=
  { TransCmp.compareOfLessAndEq_of_le lt_irrefl lt_trans not_lt le_antisymm with
    cmp_iff_lt := compareOfLessAndEq_eq_lt }

@[deprecated "Std.LawfulLECmp.compareOfLessAndEq_of_lt_irrefl_of_lt_trans_of_not_lt_of_le_antisymm"
  (since := "2025-07-01")]
protected theorem LECmp.compareOfLessAndEq
    [LT α] [DecidableRel (LT.lt (α := α))] [DecidableEq α] [LE α]
    (lt_irrefl : ∀ x : α, ¬x < x)
    (lt_trans : ∀ {x y z : α}, x < y → y < z → x < z)
    (not_lt : ∀ {x y : α}, ¬x < y ↔ y ≤ x)
    (le_antisymm : ∀ {x y : α}, x ≤ y → y ≤ x → x = y) :
    LECmp (α := α) (compareOfLessAndEq · ·) :=
  have := TransCmp.compareOfLessAndEq_of_le lt_irrefl lt_trans not_lt.1 le_antisymm
  { this with
    cmp_iff_le := (this.cmp_ne_gt).trans <| (not_congr compareOfLessAndEq_eq_lt).trans not_lt }

@[deprecated "Std.LawfulCmp.compareOfLessAndEq_of_lt_irrefl_of_lt_trans_of_not_lt_of_le_antisymm"
  (since := "2025-07-01")]
protected theorem LawfulCmp.compareOfLessAndEq
    [LT α] [DecidableRel (LT.lt (α := α))] [DecidableEq α] [BEq α] [LawfulBEq α] [LE α]
    (lt_irrefl : ∀ x : α, ¬x < x)
    (lt_trans : ∀ {x y z : α}, x < y → y < z → x < z)
    (not_lt : ∀ {x y : α}, ¬x < y ↔ y ≤ x)
    (le_antisymm : ∀ {x y : α}, x ≤ y → y ≤ x → x = y) :
    LawfulCmp (α := α) (compareOfLessAndEq · ·) :=
  { TransCmp.compareOfLessAndEq_of_le lt_irrefl lt_trans not_lt.1 le_antisymm,
    LTCmp.compareOfLessAndEq_of_le lt_irrefl lt_trans not_lt.1 le_antisymm,
    LECmp.compareOfLessAndEq lt_irrefl lt_trans not_lt le_antisymm,
    BEqCmp.compareOfLessAndEq lt_irrefl with }

@[deprecated "LawfulLTCmp.eq_compareOfLessAndEq" (since := "2025-07-01")]
theorem LTCmp.eq_compareOfLessAndEq
    [LT α] [DecidableEq α] [BEq α] [LawfulBEq α] [BEqCmp cmp] [LTCmp cmp]
    (x y : α) [Decidable (x < y)] : cmp x y = compareOfLessAndEq x y := by
  simp [compareOfLessAndEq]
  split <;> rename_i h1 <;> [skip; split <;> rename_i h2]
  · exact LTCmp.cmp_iff_lt.2 h1
  · exact BEqCmp.cmp_iff_eq.2 h2
  · cases e : cmp x y
    · cases h1 (LTCmp.cmp_iff_lt.1 e)
    · cases h2 (BEqCmp.cmp_iff_eq.1 e)
    · rfl

instance [inst₁ : OrientedCmp cmp₁] [inst₂ : OrientedCmp cmp₂] :
    OrientedCmp (compareLex cmp₁ cmp₂) where
  symm _ _ := by simp [compareLex, Ordering.swap_then]; rw [inst₁.symm, inst₂.symm]

instance [inst₁ : TransCmp cmp₁] [inst₂ : TransCmp cmp₂] :
    TransCmp (compareLex cmp₁ cmp₂) where
  le_trans {a b c} h1 h2 := by
    simp only [compareLex, ne_eq, Ordering.then_eq_gt, not_or, not_and] at h1 h2 ⊢
    refine ⟨inst₁.le_trans h1.1 h2.1, fun e1 e2 => ?_⟩
    match ab : cmp₁ a b with
    | .gt => exact h1.1 ab
    | .eq => exact inst₂.le_trans (h1.2 ab) (h2.2 (inst₁.cmp_congr_left ab ▸ e1)) e2
    | .lt => exact h2.1 <| (inst₁.cmp_eq_gt).2 (inst₁.cmp_congr_left e1 ▸ ab)

instance [Ord β] [OrientedOrd β] (f : α → β) : OrientedCmp (compareOn f) where
  symm _ _ := OrientedCmp.symm (α := β) ..

instance [Ord β] [TransOrd β] (f : α → β) : TransCmp (compareOn f) where
  le_trans := TransCmp.le_trans (α := β)

section «non-canonical instances»
-- Note: the following instances seem to cause lean to fail, see:
-- https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/Typeclass.20inference.20crashes/near/432836360

/-- Local instance for `OrientedOrd lexOrd`. -/
@[deprecated "instance exists" (since := "2025-07-01")]
theorem OrientedOrd.instLexOrd [Ord α] [Ord β]
    [OrientedOrd α] [OrientedOrd β] : @OrientedOrd (α × β) lexOrd := by
  rw [OrientedOrd, lexOrd_def]; infer_instance

/-- Local instance for `TransOrd lexOrd`. -/
@[deprecated "instance exists" (since := "2025-07-01")]
theorem TransOrd.instLexOrd [Ord α] [Ord β]
    [TransOrd α] [TransOrd β] : @TransOrd (α × β) lexOrd := by
  rw [TransOrd, lexOrd_def]; infer_instance

/-- Local instance for `OrientedOrd ord.opposite`. -/
@[deprecated "Std.OrientedOrd.opposite" (since := "2025-07-01")]
theorem OrientedOrd.instOpposite [ord : Ord α] [inst : OrientedOrd α] :
    @OrientedOrd _ ord.opposite where symm _ _ := inst.symm ..

/-- Local instance for `TransOrd ord.opposite`. -/
@[deprecated "Std.TransOrd.opposite" (since := "2025-07-01")]
theorem TransOrd.instOpposite [ord : Ord α] [inst : TransOrd α] : @TransOrd _ ord.opposite :=
  { OrientedOrd.instOpposite with le_trans := fun h1 h2 => inst.le_trans h2 h1 }

/-- Local instance for `OrientedOrd (ord.on f)`. -/
@[deprecated "Std.OrientedOrd.instOn" (since := "2025-07-01")]
theorem OrientedOrd.instOn [ord : Ord β] [OrientedOrd β] (f : α → β) : @OrientedOrd _ (ord.on f) :=
  inferInstanceAs (@OrientedCmp _ (compareOn f))

/-- Local instance for `TransOrd (ord.on f)`. -/
@[deprecated "Std.TransOrd.instOn" (since := "2025-07-01")]
theorem TransOrd.instOn [ord : Ord β] [TransOrd β] (f : α → β) : @TransOrd _ (ord.on f) :=
  inferInstanceAs (@TransCmp _ (compareOn f))

/-- Local instance for `OrientedOrd (oα.lex oβ)`. -/
@[deprecated "instance exists" (since := "2025-07-01")]
theorem OrientedOrd.instOrdLex [oα : Ord α] [oβ : Ord β] [OrientedOrd α] [OrientedOrd β] :
    @OrientedOrd _ (oα.lex oβ) := OrientedOrd.instLexOrd

/-- Local instance for `TransOrd (oα.lex oβ)`. -/
@[deprecated "instance exists" (since := "2025-07-01")]
theorem TransOrd.instOrdLex [oα : Ord α] [oβ : Ord β] [TransOrd α] [TransOrd β] :
    @TransOrd _ (oα.lex oβ) := TransOrd.instLexOrd

/-- Local instance for `OrientedOrd (oα.lex' oβ)`. -/
@[deprecated "Std.OrientedOrd.instOrdLex'" (since := "2025-07-01")]
theorem OrientedOrd.instOrdLex' (ord₁ ord₂ : Ord α) [@OrientedOrd _ ord₁] [@OrientedOrd _ ord₂] :
    @OrientedOrd _ (ord₁.lex' ord₂) :=
  inferInstanceAs (OrientedCmp (compareLex ord₁.compare ord₂.compare))

/-- Local instance for `TransOrd (oα.lex' oβ)`. -/
@[deprecated "Std.TransOrd.instOrdLex'" (since := "2025-07-01")]
theorem TransOrd.instOrdLex' (ord₁ ord₂ : Ord α) [@TransOrd _ ord₁] [@TransOrd _ ord₂] :
    @TransOrd _ (ord₁.lex' ord₂) :=
  inferInstanceAs (TransCmp (compareLex ord₁.compare ord₂.compare))

end «non-canonical instances»

instance : LawfulOrd Nat := .compareOfLessAndEq
  Nat.lt_irrefl Nat.lt_trans Nat.not_lt Nat.le_antisymm

instance : LawfulOrd (Fin n) where
  symm _ _ := OrientedCmp.symm (α := Nat) (cmp := compare) ..
  le_trans := TransCmp.le_trans (α := Nat) (cmp := compare)
  cmp_iff_beq := (BEqCmp.cmp_iff_beq (α := Nat) (cmp := compare)).trans (by simp [Fin.ext_iff])
  cmp_iff_lt := LTCmp.cmp_iff_lt (α := Nat) (cmp := compare)
  cmp_iff_le := LECmp.cmp_iff_le (α := Nat) (cmp := compare)

instance : LawfulOrd Bool where
  symm := by decide
  le_trans := by decide
  cmp_iff_beq := by decide
  cmp_iff_lt := by decide
  cmp_iff_le := by decide

instance : LawfulOrd Int := .compareOfLessAndEq
  Int.lt_irrefl Int.lt_trans Int.not_lt Int.le_antisymm

end Batteries

namespace Ordering

open Batteries

instance (f : α → β) (cmp : β → β → Ordering) [OrientedCmp cmp] : OrientedCmp (byKey f cmp) where
  symm a b := OrientedCmp.symm (f a) (f b)

instance (f : α → β) (cmp : β → β → Ordering) [TransCmp cmp] : TransCmp (byKey f cmp) where
  le_trans h₁ h₂ := TransCmp.le_trans (α := β) h₁ h₂

end Ordering

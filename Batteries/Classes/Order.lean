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
theorem TransCmp.compareOfLessAndEq_of_irrefl_of_trans_of_antisymm
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
theorem TransCmp.compareOfLessAndEq_of_irrefl_of_trans_of_not_lt_of_antisymm
    [LT α] [LE α] [DecidableLT α] [DecidableEq α]
    (lt_irrefl : ∀ x : α, ¬x < x)
    (lt_trans : ∀ {x y z : α}, x < y → y < z → x < z)
    (not_lt : ∀ {x y : α}, ¬x < y → y ≤ x)
    (le_antisymm : ∀ {x y : α}, x ≤ y → y ≤ x → x = y) :
    TransCmp (α := α) (compareOfLessAndEq · ·) :=
  .compareOfLessAndEq_of_irrefl_of_trans_of_antisymm
    lt_irrefl lt_trans fun xy yx => le_antisymm (not_lt yx) (not_lt xy)

-- make redundant?
theorem LawfulLTCmp.compareOfLessAndEq_of_irrefl_of_trans_of_antisymm
    [LT α] [DecidableLT α] [DecidableEq α]
    (lt_irrefl : ∀ x : α, ¬x < x)
    (lt_trans : ∀ {x y z : α}, x < y → y < z → x < z)
    (lt_antisymm : ∀ {x y : α}, ¬x < y → ¬y < x → x = y) :
    LawfulLTCmp (α := α) (compareOfLessAndEq · ·) :=
  { TransCmp.compareOfLessAndEq_of_irrefl_of_trans_of_antisymm
      lt_irrefl lt_trans lt_antisymm with
    eq_lt_iff_lt := Batteries.compareOfLessAndEq_eq_lt }

-- make redundant?
theorem LawfulLTCmp.compareOfLessAndEq_of_irrefl_of_trans_of_not_lt_of_antisymm
    [LT α] [DecidableLT α] [DecidableEq α] [LE α]
    (lt_irrefl : ∀ x : α, ¬x < x)
    (lt_trans : ∀ {x y z : α}, x < y → y < z → x < z)
    (not_lt : ∀ {x y : α}, ¬x < y → y ≤ x)
    (le_antisymm : ∀ {x y : α}, x ≤ y → y ≤ x → x = y) :
    LawfulLTCmp (α := α) (compareOfLessAndEq · ·) :=
  { TransCmp.compareOfLessAndEq_of_irrefl_of_trans_of_not_lt_of_antisymm
      lt_irrefl lt_trans not_lt le_antisymm with
    eq_lt_iff_lt := Batteries.compareOfLessAndEq_eq_lt }

-- make redundant?
theorem LawfulLECmp.compareOfLessAndEq_of_irrefl_of_trans_of_not_lt_of_antisymm
    [LT α] [DecidableLT α] [DecidableEq α] [LE α]
    (lt_irrefl : ∀ x : α, ¬x < x)
    (lt_trans : ∀ {x y z : α}, x < y → y < z → x < z)
    (not_lt : ∀ {x y : α}, ¬x < y ↔ y ≤ x)
    (le_antisymm : ∀ {x y : α}, x ≤ y → y ≤ x → x = y) :
    LawfulLECmp (α := α) (compareOfLessAndEq · ·) :=
  have := TransCmp.compareOfLessAndEq_of_irrefl_of_trans_of_not_lt_of_antisymm
      lt_irrefl lt_trans not_lt.1 le_antisymm
  { this with
    isLE_iff_le := by
      intro x y
      simp only [Ordering.isLE_iff_ne_gt, ← not_lt]
      apply not_congr
      rw [this.gt_iff_lt, Batteries.compareOfLessAndEq_eq_lt] }

theorem LawfulCmp.compareOfLessAndEq_of_irrefl_of_trans_of_not_lt_of_antisymm
    [LT α] [LE α] [DecidableLT α] [DecidableLE α] [DecidableEq α]
    (lt_irrefl : ∀ x : α, ¬x < x)
    (lt_trans : ∀ {x y z : α}, x < y → y < z → x < z)
    (not_lt : ∀ {x y : α}, ¬x < y ↔ y ≤ x)
    (le_antisymm : ∀ {x y : α}, x ≤ y → y ≤ x → x = y) :
    LawfulCmp (α := α) (compareOfLessAndEq · ·) :=
    have instT := TransCmp.compareOfLessAndEq_of_irrefl_of_trans_of_not_lt_of_antisymm
      lt_irrefl lt_trans not_lt.1 le_antisymm
    have instLT := LawfulLTCmp.compareOfLessAndEq_of_irrefl_of_trans_of_not_lt_of_antisymm
      lt_irrefl lt_trans not_lt.1 le_antisymm
    have instLE := LawfulLECmp.compareOfLessAndEq_of_irrefl_of_trans_of_not_lt_of_antisymm
      lt_irrefl lt_trans not_lt le_antisymm
    have le_refl (x : α) : x ≤ x := by rw [← not_lt]; exact lt_irrefl _
    have not_le {x y : α} : ¬x ≤ y ↔ y < x := by simp [← not_lt]
    { instT, instLT, instLE with
      eq_of_compare {_  _}:= by rw [compareOfLessAndEq_eq_eq le_refl not_le]; exact id
    }

instance : LawfulOrd Nat :=
  LawfulCmp.compareOfLessAndEq_of_irrefl_of_trans_of_not_lt_of_antisymm
    Nat.lt_irrefl Nat.lt_trans Nat.not_lt Nat.le_antisymm

instance : LawfulOrd Int :=
  LawfulCmp.compareOfLessAndEq_of_irrefl_of_trans_of_not_lt_of_antisymm
    Int.lt_irrefl Int.lt_trans Int.not_lt Int.le_antisymm

instance : LawfulOrd Bool := by
  apply LawfulCmp.mk <;> decide

instance : LawfulOrd (Fin n) where
  eq_swap := OrientedCmp.eq_swap (α := Nat) (cmp := compare) ..
  eq_lt_iff_lt := LawfulLTCmp.eq_lt_iff_lt (α := Nat) (cmp := compare)
  isLE_iff_le := LawfulLECmp.isLE_iff_le (α := Nat) (cmp := compare)
  isLE_trans := TransCmp.isLE_trans (α := Nat) (cmp := compare)

end Std

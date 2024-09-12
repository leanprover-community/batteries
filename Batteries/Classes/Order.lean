/-
Copyright (c) 2022 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Batteries.Tactic.SeqFocus

/-! ## Ordering -/

namespace Ordering

@[simp] theorem swap_swap {o : Ordering} : o.swap.swap = o := by cases o <;> rfl

@[simp] theorem swap_inj {o₁ o₂ : Ordering} : o₁.swap = o₂.swap ↔ o₁ = o₂ :=
  ⟨fun h => by simpa using congrArg swap h, congrArg _⟩

theorem swap_then (o₁ o₂ : Ordering) : (o₁.then o₂).swap = o₁.swap.then o₂.swap := by
  cases o₁ <;> rfl

theorem then_eq_lt {o₁ o₂ : Ordering} : o₁.then o₂ = lt ↔ o₁ = lt ∨ o₁ = eq ∧ o₂ = lt := by
  cases o₁ <;> cases o₂ <;> decide

theorem then_eq_eq {o₁ o₂ : Ordering} : o₁.then o₂ = eq ↔ o₁ = eq ∧ o₂ = eq := by
  cases o₁ <;> simp [«then»]

theorem then_eq_gt {o₁ o₂ : Ordering} : o₁.then o₂ = gt ↔ o₁ = gt ∨ o₁ = eq ∧ o₂ = gt := by
  cases o₁ <;> cases o₂ <;> decide

end Ordering

namespace Batteries

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

theorem cmp_ne_gt [OrientedCmp cmp] : cmp x y ≠ .gt ↔ cmp y x ≠ .lt := not_congr cmp_eq_gt

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

theorem cmp_congr_right (yz : cmp y z = .eq) : cmp x y = cmp x z := by
  rw [← Ordering.swap_inj, symm, symm, cmp_congr_left yz]

end TransCmp

instance [inst : OrientedCmp cmp] : OrientedCmp (flip cmp) where
  symm _ _ := inst.symm ..

instance [inst : TransCmp cmp] : TransCmp (flip cmp) where
  le_trans h1 h2 := inst.le_trans h2 h1

/-- `BEqCmp cmp` asserts that `cmp x y = .eq` and `x == y` coincide. -/
class BEqCmp [BEq α] (cmp : α → α → Ordering) : Prop where
  /-- `cmp x y = .eq` holds iff `x == y` is true. -/
  cmp_iff_beq : cmp x y = .eq ↔ x == y

theorem BEqCmp.cmp_iff_eq [BEq α] [LawfulBEq α] [BEqCmp (α := α) cmp] : cmp x y = .eq ↔ x = y := by
  simp [BEqCmp.cmp_iff_beq]

/-- `LTCmp cmp` asserts that `cmp x y = .lt` and `x < y` coincide. -/
class LTCmp [LT α] (cmp : α → α → Ordering) extends OrientedCmp cmp : Prop where
  /-- `cmp x y = .lt` holds iff `x < y` is true. -/
  cmp_iff_lt : cmp x y = .lt ↔ x < y

theorem LTCmp.cmp_iff_gt [LT α] [LTCmp (α := α) cmp] : cmp x y = .gt ↔ y < x := by
  rw [OrientedCmp.cmp_eq_gt, LTCmp.cmp_iff_lt]

/-- `LECmp cmp` asserts that `cmp x y ≠ .gt` and `x ≤ y` coincide. -/
class LECmp [LE α] (cmp : α → α → Ordering) extends OrientedCmp cmp : Prop where
  /-- `cmp x y ≠ .gt` holds iff `x ≤ y` is true. -/
  cmp_iff_le : cmp x y ≠ .gt ↔ x ≤ y

theorem LECmp.cmp_iff_ge [LE α] [LECmp (α := α) cmp] : cmp x y ≠ .lt ↔ y ≤ x := by
  rw [← OrientedCmp.cmp_ne_gt, LECmp.cmp_iff_le]

/-- `LawfulCmp cmp` asserts that the `LE`, `LT`, `BEq` instances are all coherent with each other
and with `cmp`, describing a strict weak order (a linear order except for antisymmetry). -/
class LawfulCmp [LE α] [LT α] [BEq α] (cmp : α → α → Ordering) extends
  TransCmp cmp, BEqCmp cmp, LTCmp cmp, LECmp cmp : Prop

/-- `OrientedOrd α` asserts that the `Ord` instance satisfies `OrientedCmp`. -/
abbrev OrientedOrd (α) [Ord α] := OrientedCmp (α := α) compare

/-- `TransOrd α` asserts that the `Ord` instance satisfies `TransCmp`. -/
abbrev TransOrd (α) [Ord α] := TransCmp (α := α) compare

/-- `BEqOrd α` asserts that the `Ord` and `BEq` instances are coherent via `BEqCmp`. -/
abbrev BEqOrd (α) [BEq α] [Ord α] := BEqCmp (α := α) compare

/-- `LTOrd α` asserts that the `Ord` instance satisfies `LTCmp`. -/
abbrev LTOrd (α) [LT α] [Ord α] := LTCmp (α := α) compare

/-- `LEOrd α` asserts that the `Ord` instance satisfies `LECmp`. -/
abbrev LEOrd (α) [LE α] [Ord α] := LECmp (α := α) compare

/-- `LawfulOrd α` asserts that the `Ord` instance satisfies `LawfulCmp`. -/
abbrev LawfulOrd (α) [LE α] [LT α] [BEq α] [Ord α] := LawfulCmp (α := α) compare

theorem compareOfLessAndEq_eq_lt {x y : α} [LT α] [Decidable (x < y)] [DecidableEq α] :
    compareOfLessAndEq x y = .lt ↔ x < y := by
  simp [compareOfLessAndEq]
  split <;> simp

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

protected theorem TransCmp.compareOfLessAndEq_of_le
    [LT α] [LE α] [DecidableRel (LT.lt (α := α))] [DecidableEq α]
    (lt_irrefl : ∀ x : α, ¬x < x)
    (lt_trans : ∀ {x y z : α}, x < y → y < z → x < z)
    (not_lt : ∀ {x y : α}, ¬x < y → y ≤ x)
    (le_antisymm : ∀ {x y : α}, x ≤ y → y ≤ x → x = y) :
    TransCmp (α := α) (compareOfLessAndEq · ·) :=
  .compareOfLessAndEq lt_irrefl lt_trans fun xy yx => le_antisymm (not_lt yx) (not_lt xy)

protected theorem BEqCmp.compareOfLessAndEq
    [LT α] [DecidableRel (LT.lt (α := α))] [DecidableEq α] [BEq α] [LawfulBEq α]
    (lt_irrefl : ∀ x : α, ¬x < x) :
    BEqCmp (α := α) (compareOfLessAndEq · ·) where
  cmp_iff_beq {x y} := by
    simp [compareOfLessAndEq]
    split <;> [skip; split] <;> simp [*]
    rintro rfl; exact lt_irrefl _ ‹_›

protected theorem LTCmp.compareOfLessAndEq
    [LT α] [DecidableRel (LT.lt (α := α))] [DecidableEq α]
    (lt_irrefl : ∀ x : α, ¬x < x)
    (lt_trans : ∀ {x y z : α}, x < y → y < z → x < z)
    (lt_antisymm : ∀ {x y : α}, ¬x < y → ¬y < x → x = y) :
    LTCmp (α := α) (compareOfLessAndEq · ·) :=
  { TransCmp.compareOfLessAndEq lt_irrefl lt_trans lt_antisymm with
    cmp_iff_lt := compareOfLessAndEq_eq_lt }

protected theorem LTCmp.compareOfLessAndEq_of_le
    [LT α] [DecidableRel (LT.lt (α := α))] [DecidableEq α] [LE α]
    (lt_irrefl : ∀ x : α, ¬x < x)
    (lt_trans : ∀ {x y z : α}, x < y → y < z → x < z)
    (not_lt : ∀ {x y : α}, ¬x < y → y ≤ x)
    (le_antisymm : ∀ {x y : α}, x ≤ y → y ≤ x → x = y) :
    LTCmp (α := α) (compareOfLessAndEq · ·) :=
  { TransCmp.compareOfLessAndEq_of_le lt_irrefl lt_trans not_lt le_antisymm with
    cmp_iff_lt := compareOfLessAndEq_eq_lt }

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

theorem _root_.lexOrd_def [Ord α] [Ord β] :
    (lexOrd : Ord (α × β)).compare = compareLex (compareOn (·.1)) (compareOn (·.2)) := rfl

section «non-canonical instances»
-- Note: the following instances seem to cause lean to fail, see:
-- https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/Typeclass.20inference.20crashes/near/432836360

/-- Local instance for `OrientedOrd lexOrd`. -/
theorem OrientedOrd.instLexOrd [Ord α] [Ord β]
    [OrientedOrd α] [OrientedOrd β] : @OrientedOrd (α × β) lexOrd := by
  rw [OrientedOrd, lexOrd_def]; infer_instance

/-- Local instance for `TransOrd lexOrd`. -/
theorem TransOrd.instLexOrd [Ord α] [Ord β]
    [TransOrd α] [TransOrd β] : @TransOrd (α × β) lexOrd := by
  rw [TransOrd, lexOrd_def]; infer_instance

/-- Local instance for `OrientedOrd ord.opposite`. -/
theorem OrientedOrd.instOpposite [ord : Ord α] [inst : OrientedOrd α] :
    @OrientedOrd _ ord.opposite where symm _ _ := inst.symm ..

/-- Local instance for `TransOrd ord.opposite`. -/
theorem TransOrd.instOpposite [ord : Ord α] [inst : TransOrd α] : @TransOrd _ ord.opposite :=
  { OrientedOrd.instOpposite with le_trans := fun h1 h2 => inst.le_trans h2 h1 }

/-- Local instance for `OrientedOrd (ord.on f)`. -/
theorem OrientedOrd.instOn [ord : Ord β] [OrientedOrd β] (f : α → β) : @OrientedOrd _ (ord.on f) :=
  inferInstanceAs (@OrientedCmp _ (compareOn f))

/-- Local instance for `TransOrd (ord.on f)`. -/
theorem TransOrd.instOn [ord : Ord β] [TransOrd β] (f : α → β) : @TransOrd _ (ord.on f) :=
  inferInstanceAs (@TransCmp _ (compareOn f))

/-- Local instance for `OrientedOrd (oα.lex oβ)`. -/
theorem OrientedOrd.instOrdLex [oα : Ord α] [oβ : Ord β] [OrientedOrd α] [OrientedOrd β] :
    @OrientedOrd _ (oα.lex oβ) := OrientedOrd.instLexOrd

/-- Local instance for `TransOrd (oα.lex oβ)`. -/
theorem TransOrd.instOrdLex [oα : Ord α] [oβ : Ord β] [TransOrd α] [TransOrd β] :
    @TransOrd _ (oα.lex oβ) := TransOrd.instLexOrd

/-- Local instance for `OrientedOrd (oα.lex' oβ)`. -/
theorem OrientedOrd.instOrdLex' (ord₁ ord₂ : Ord α) [@OrientedOrd _ ord₁] [@OrientedOrd _ ord₂] :
    @OrientedOrd _ (ord₁.lex' ord₂) :=
  inferInstanceAs (OrientedCmp (compareLex ord₁.compare ord₂.compare))

/-- Local instance for `TransOrd (oα.lex' oβ)`. -/
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

/-- Pull back a comparator by a function `f`, by applying the comparator to both arguments. -/
@[inline] def byKey (f : α → β) (cmp : β → β → Ordering) (a b : α) : Ordering := cmp (f a) (f b)

instance (f : α → β) (cmp : β → β → Ordering) [OrientedCmp cmp] : OrientedCmp (byKey f cmp) where
  symm a b := OrientedCmp.symm (f a) (f b)

instance (f : α → β) (cmp : β → β → Ordering) [TransCmp cmp] : TransCmp (byKey f cmp) where
  le_trans h₁ h₂ := TransCmp.le_trans (α := β) h₁ h₂

end Ordering

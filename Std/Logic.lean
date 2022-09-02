/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/

/- not -/

/-- Ex falso for negation. From `¬ a` and `a` anything follows. This is the same as `absurd` with
the arguments flipped, but it is in the `not` namespace so that projection notation can be used. -/
def Not.elim {α : Sort _} (H1 : ¬a) (H2 : a) : α := absurd H2 H1

theorem not_congr (h : a ↔ b) : ¬a ↔ ¬b := ⟨mt h.2, mt h.1⟩

/-! Declarations about `iff` -/

theorem iff_of_true (ha : a) (hb : b) : a ↔ b := ⟨λ_ => hb, λ _ => ha⟩

theorem iff_of_false (ha : ¬a) (hb : ¬b) : a ↔ b := ⟨ha.elim, hb.elim⟩

/- or simp rules -/

-- Port note: in mathlib3, this is not_or
theorem not_or_intro {a b : Prop} : ¬ a → ¬ b → ¬ (a ∨ b)
  | hna, _, .inl ha => absurd ha hna
  | _, hnb, .inr hb => absurd hb hnb

/- or resolution rules -/

theorem Or.resolve_left {a b : Prop} (h: a ∨ b) (na : ¬ a) : b := h.elim (absurd · na) id

theorem Or.neg_resolve_left (h : ¬a ∨ b) (ha : a) : b := h.elim (absurd ha) id

theorem Or.resolve_right {a b : Prop} (h: a ∨ b) (nb : ¬ b) : a := h.elim id (absurd · nb)

theorem Or.neg_resolve_right (h : a ∨ ¬b) (nb : b) : a := h.elim id (absurd nb)

/- Boolean order classes -/

/-- `TotalBLE le` asserts that `le` has a total order, that is, `le a b ∨ le b a`. -/
class TotalBLE (le : α → α → Bool) : Prop where
  /-- `le` is total: either `le a b` or `le b a`. -/
  total : le a b ∨ le b a

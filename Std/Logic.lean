/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad, Floris van Doorn, Mario Carneiro
-/
import Std.Tactic.Basic

instance {f : α → β} [DecidablePred p] : DecidablePred (p ∘ f) :=
  inferInstanceAs <| DecidablePred fun x => p (f x)

/-! ## not -/

theorem Not.intro {a : Prop} (h : a → False) : ¬ a := h

/-- Ex falso for negation. From `¬ a` and `a` anything follows. This is the same as `absurd` with
the arguments flipped, but it is in the `not` namespace so that projection notation can be used. -/
def Not.elim {α : Sort _} (H1 : ¬a) (H2 : a) : α := absurd H2 H1

theorem Not.imp {a b : Prop} (H2 : ¬b) (H1 : a → b) : ¬a := mt H1 H2

theorem not_congr (h : a ↔ b) : ¬a ↔ ¬b := ⟨mt h.2, mt h.1⟩

theorem not_not_not (a : Prop) : ¬¬¬a ↔ ¬a := ⟨mt not_not_intro, not_not_intro⟩

/-! ## iff -/

/-- Non-dependent eliminator for `Iff`. -/
def Iff.elim (f : (a → b) → (b → a) → α) (h : a ↔ b) : α := f h.1 h.2

theorem Eq.to_iff : a = b → (a ↔ b) | rfl => Iff.rfl

theorem neq_of_not_iff : ¬(a ↔ b) → a ≠ b := mt Eq.to_iff

theorem of_iff_true (h : a ↔ True) : a := h.2 ⟨⟩

theorem not_of_iff_false : (a ↔ False) → ¬a := Iff.mp

theorem iff_of_true (ha : a) (hb : b) : a ↔ b := ⟨fun _ => hb, fun _ => ha⟩

theorem iff_of_false (ha : ¬a) (hb : ¬b) : a ↔ b := ⟨ha.elim, hb.elim⟩

theorem iff_true_intro (h : a) : a ↔ True := iff_of_true h ⟨⟩

theorem iff_false_intro (h : ¬a) : a ↔ False := iff_of_false h id

theorem not_iff_false_intro (h : a) : ¬a ↔ False := iff_false_intro (not_not_intro h)

theorem imp_congr_left (h : a ↔ b) : (a → c) ↔ (b → c) :=
  ⟨fun hac ha => hac (h.2 ha), fun hbc ha => hbc (h.1 ha)⟩

theorem imp_congr_right (h : a → (b ↔ c)) : (a → b) ↔ (a → c) :=
  ⟨fun hab ha => (h ha).1 (hab ha), fun hcd ha => (h ha).2 (hcd ha)⟩

theorem imp_congr_ctx (h₁ : a ↔ c) (h₂ : c → (b ↔ d)) : (a → b) ↔ (c → d) :=
  (imp_congr_left h₁).trans (imp_congr_right h₂)

theorem imp_congr (h₁ : a ↔ c) (h₂ : b ↔ d) : (a → b) ↔ (c → d) := imp_congr_ctx h₁ fun _ => h₂

theorem iff_congr (h₁ : a ↔ c) (h₂ : b ↔ d) : (a ↔ b) ↔ (c ↔ d) :=
  ⟨fun h => h₁.symm.trans <| h.trans h₂, fun h => h₁.trans <| h.trans h₂.symm⟩

@[simp] theorem not_true : (¬ True) ↔ False := iff_false_intro (not_not_intro ⟨⟩)

@[simp] theorem not_false_iff : (¬ False) ↔ True := iff_true_intro not_false

theorem ne_self_iff_false (a : α) : a ≠ a ↔ False := not_iff_false_intro rfl

theorem eq_self_iff_true (a : α) : a = a ↔ True := iff_true_intro rfl

theorem heq_self_iff_true (a : α) : HEq a a ↔ True := iff_true_intro HEq.rfl

theorem iff_not_self : ¬(a ↔ ¬a) | H => let f h := H.1 h h; f (H.2 f)

@[simp] theorem not_iff_self : ¬(¬a ↔ a) | H => iff_not_self H.symm

theorem true_iff_false : (True ↔ False) ↔ False := iff_false_intro (fun h => h.1 ⟨⟩)

theorem false_iff_true : (False ↔ True) ↔ False := iff_false_intro (fun h => h.2 ⟨⟩)

theorem false_of_true_iff_false : (True ↔ False) → False := fun h => h.1 ⟨⟩

theorem false_of_true_eq_false : (True = False) → False := fun h => h ▸ trivial

theorem true_eq_false_of_false : False → (True = False) := False.elim

theorem eq_comm {a b : α} : a = b ↔ b = a := ⟨Eq.symm, Eq.symm⟩

-- This is not marked `@[simp]` because we have `implies_true : (α → True) = True` in core.
theorem implies_true_iff (α : Sort u) : (α → True) ↔ True := iff_true_intro fun _ => trivial

theorem false_implies_iff (a : Prop) : (False → a) ↔ True := iff_true_intro False.elim

theorem true_implies_iff (α : Prop) : (True → α) ↔ α := ⟨fun h => h trivial, fun h _ => h⟩

/-! ## and -/

/-- Non-dependent eliminator for `And`. -/
abbrev And.elim (f : a → b → α) (h : a ∧ b) : α := f h.1 h.2

theorem And.symm : a ∧ b → b ∧ a | ⟨ha, hb⟩ => ⟨hb, ha⟩

theorem And.imp (f : a → c) (g : b → d) (h : a ∧ b) : c ∧ d := ⟨f h.1, g h.2⟩

theorem And.imp_left (h : a → b) : a ∧ c → b ∧ c := .imp h id

theorem And.imp_right (h : a → b) : c ∧ a → c ∧ b := .imp id h

theorem and_congr (h₁ : a ↔ c) (h₂ : b ↔ d) : a ∧ b ↔ c ∧ d :=
  ⟨And.imp h₁.1 h₂.1, And.imp h₁.2 h₂.2⟩

theorem and_comm : a ∧ b ↔ b ∧ a := And.comm

theorem and_congr_right (h : a → (b ↔ c)) : (a ∧ b) ↔ (a ∧ c) :=
⟨fun ⟨ha, hb⟩ => ⟨ha, (h ha).1 hb⟩, fun ⟨ha, hb⟩ => ⟨ha, (h ha).2 hb⟩⟩

theorem and_congr_left (h : c → (a ↔ b)) : a ∧ c ↔ b ∧ c :=
  and_comm.trans <| (and_congr_right h).trans and_comm

theorem and_congr_left' (h : a ↔ b) : a ∧ c ↔ b ∧ c := and_congr h .rfl

theorem and_congr_right' (h : b ↔ c) : a ∧ b ↔ a ∧ c := and_congr .rfl h

theorem and_assoc : (a ∧ b) ∧ c ↔ a ∧ (b ∧ c) :=
  ⟨fun ⟨⟨ha, hb⟩, hc⟩ => ⟨ha, hb, hc⟩, fun ⟨ha, hb, hc⟩ => ⟨⟨ha, hb⟩, hc⟩⟩

theorem and_left_comm : a ∧ (b ∧ c) ↔ b ∧ (a ∧ c) := by
  rw [← and_assoc, ← and_assoc, @and_comm a b]

theorem and_right_comm : (a ∧ b) ∧ c ↔ (a ∧ c) ∧ b := by
  simp only [and_left_comm, and_comm]; rfl

theorem And.rotate : a ∧ b ∧ c ↔ b ∧ c ∧ a := by
  simp only [and_left_comm, and_comm]; rfl

theorem and_iff_left_of_imp {a b : Prop} (h : a → b) : (a ∧ b) ↔ a :=
  ⟨And.left, fun ha => ⟨ha, h ha⟩⟩

theorem and_iff_right_of_imp {a b : Prop} (h : b → a) : (a ∧ b) ↔ b :=
  ⟨And.right, fun hb => ⟨h hb, hb⟩⟩

theorem and_iff_left (hb : b) : a ∧ b ↔ a := and_iff_left_of_imp fun _ => hb

theorem and_iff_right (ha : a) : a ∧ b ↔ b := and_iff_right_of_imp fun _ => ha

@[simp] theorem and_iff_left_iff_imp {a b : Prop} : ((a ∧ b) ↔ a) ↔ (a → b) :=
  ⟨fun h ha => (h.2 ha).2, and_iff_left_of_imp⟩

@[simp] theorem and_iff_right_iff_imp {a b : Prop} : ((a ∧ b) ↔ b) ↔ (b → a) :=
  ⟨fun h ha => (h.2 ha).1, and_iff_right_of_imp⟩

@[simp] theorem iff_self_and {p q : Prop} : (p ↔ p ∧ q) ↔ (p → q) := by
  rw [@Iff.comm p, and_iff_left_iff_imp]

@[simp] theorem iff_and_self {p q : Prop} : (p ↔ q ∧ p) ↔ (p → q) := by rw [and_comm, iff_self_and]

@[simp] theorem and_congr_right_iff : (a ∧ b ↔ a ∧ c) ↔ (a → (b ↔ c)) :=
  ⟨fun h ha => by simp [ha] at h; exact h, and_congr_right⟩

@[simp] theorem and_congr_left_iff : (a ∧ c ↔ b ∧ c) ↔ c → (a ↔ b) := by
  simp only [and_comm, ← and_congr_right_iff]; rfl

@[simp] theorem and_self_left : a ∧ a ∧ b ↔ a ∧ b :=
  ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, h.1, h.2⟩⟩

@[simp] theorem and_self_right : (a ∧ b) ∧ b ↔ a ∧ b :=
  ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, h.2⟩, h.2⟩⟩

theorem not_and_of_not_left (b : Prop) : ¬a → ¬(a ∧ b) := mt And.left

theorem not_and_of_not_right (a : Prop) {b : Prop} : ¬b → ¬(a ∧ b) := mt And.right

@[simp] theorem and_not_self : ¬(a ∧ ¬a) | ⟨ha, hn⟩ => hn ha

@[simp] theorem not_and_self : ¬(¬a ∧ a) | ⟨hn, ha⟩ => hn ha

theorem and_not_self_iff (a : Prop) : a ∧ ¬ a ↔ False := iff_false_intro and_not_self

theorem not_and_self_iff (a : Prop) : ¬ a ∧ a ↔ False := iff_false_intro not_and_self

/-! ## or -/

theorem not_not_em (a : Prop) : ¬¬(a ∨ ¬a) := fun h => h (.inr (h ∘ .inl))

theorem Or.symm : a ∨ b → b ∨ a := .rec .inr .inl

theorem Or.imp (f : a → c) (g : b → d) (h : a ∨ b) : c ∨ d := h.elim (inl ∘ f) (inr ∘ g)

theorem Or.imp_left (f : a → b) : a ∨ c → b ∨ c := .imp f id

theorem Or.imp_right (f : b → c) : a ∨ b → a ∨ c := .imp id f

theorem or_congr (h₁ : a ↔ c) (h₂ : b ↔ d) : (a ∨ b) ↔ (c ∨ d) := ⟨.imp h₁.1 h₂.1, .imp h₁.2 h₂.2⟩

theorem Or.comm : a ∨ b ↔ b ∨ a := ⟨Or.symm, Or.symm⟩

theorem or_comm (a b : Prop) : a ∨ b ↔ b ∨ a := Or.comm

theorem or_assoc (a b : Prop) : (a ∨ b) ∨ c ↔ a ∨ (b ∨ c) :=
  ⟨.rec (.imp_right .inl) (.inr ∘ .inr), .rec (.inl ∘ .inl) (.imp_left .inr)⟩

theorem Or.resolve_left {a b : Prop} (h: a ∨ b) (na : ¬ a) : b := h.elim (absurd · na) id

theorem Or.neg_resolve_left (h : ¬a ∨ b) (ha : a) : b := h.elim (absurd ha) id

theorem Or.resolve_right {a b : Prop} (h: a ∨ b) (nb : ¬ b) : a := h.elim id (absurd · nb)

theorem Or.neg_resolve_right (h : a ∨ ¬b) (nb : b) : a := h.elim id (absurd nb)

theorem or_left_comm : a ∨ (b ∨ c) ↔ b ∨ (a ∨ c) := by rw [← or_assoc, ← or_assoc, @or_comm a b]

theorem or_iff_right_of_imp (ha : a → b) : (a ∨ b) ↔ b := ⟨Or.rec ha id, .inr⟩

theorem or_iff_left_of_imp (hb : b → a) : (a ∨ b) ↔ a := ⟨Or.rec id hb, .inl⟩

theorem not_or_intro {a b : Prop} (ha : ¬ a) (hb : ¬ b) : ¬ (a ∨ b) := (·.elim ha hb)

theorem not_or : ¬ (p ∨ q) ↔ ¬ p ∧ ¬ q :=
  ⟨fun H => ⟨mt .inl H, mt .inr H⟩, fun ⟨hp, hq⟩ => not_or_intro hp hq⟩

/-! ## distributivity -/

/-- `∧` distributes over `∨` (on the left). -/
theorem and_or_distrib_left : a ∧ (b ∨ c) ↔ (a ∧ b) ∨ (a ∧ c) :=
  ⟨fun ⟨ha, hbc⟩ => hbc.imp (.intro ha) (.intro ha), Or.rec (.imp_right .inl) (.imp_right .inr)⟩

/-- `∧` distributes over `∨` (on the right). -/
theorem or_and_distrib_right : (a ∨ b) ∧ c ↔ (a ∧ c) ∨ (b ∧ c) := by
  simp [and_comm, and_or_distrib_left]

/-- `∨` distributes over `∧` (on the left). -/
theorem or_and_distrib_left : a ∨ (b ∧ c) ↔ (a ∨ b) ∧ (a ∨ c) :=
  ⟨Or.rec (fun ha => ⟨.inl ha, .inl ha⟩) (.imp .inr .inr),
   And.rec <| .rec (fun _ => .inl ·) (.imp_right ∘ .intro)⟩

/-- `∨` distributes over `∧` (on the right). -/
theorem and_or_distrib_right : (a ∧ b) ∨ c ↔ (a ∨ c) ∧ (b ∨ c) := by
  simp [or_comm, or_and_distrib_left]

@[simp] theorem or_self_left : a ∨ a ∨ b ↔ a ∨ b := ⟨.rec .inl id, .rec .inl (.inr ∘ .inr)⟩

@[simp] theorem or_self_right : (a ∨ b) ∨ b ↔ a ∨ b := ⟨.rec id .inr, .rec (.inl ∘ .inl) .inr⟩

/-! ## exists and forall -/

-- Port note: this is `forall_congr` from Lean 3. In Lean 4, there is already something
-- with that name and a slightly different type.
theorem forall_congr' {p q : α → Prop} (h : ∀ a, p a ↔ q a) : (∀ a, p a) ↔ ∀ a, q a :=
  ⟨fun H a => (h a).1 (H a), fun H a => (h a).2 (H a)⟩

theorem Exists.imp {p q : α → Prop} (h : ∀ a, p a → q a) : (∃ a, p a) → ∃ a, q a
  | ⟨a, hp⟩ => ⟨a, h a hp⟩

theorem exists_congr {p q : α → Prop} (h : ∀ a, p a ↔ q a) : (∃ a, p a) ↔ ∃ a, q a :=
  ⟨Exists.imp fun x => (h x).1, Exists.imp fun x => (h x).2⟩

theorem forall_not_of_not_exists {p : α → Prop} (hne : ¬∃ x, p x) (x) : ¬p x | hp => hne ⟨x, hp⟩

@[simp] theorem exists_false : ¬ (∃ _a : α, False) := fun ⟨_, h⟩ => h

/- decidable -/

theorem Decidable.not_not (p) [Decidable p] : ¬¬p ↔ p := ⟨of_not_not, not_not_intro⟩

/-- Construct a non-Prop by cases on an `Or`, when the left conjunct is decidable. -/
protected def Or.by_cases [Decidable p] {α : Sort u} (h : p ∨ q) (h₁ : p → α) (h₂ : q → α) : α :=
  if hp : p then h₁ hp else h₂ (h.resolve_left hp)

/-- Construct a non-Prop by cases on an `Or`, when the right conjunct is decidable. -/
protected def Or.by_cases' [Decidable q] {α : Sort u} (h : p ∨ q) (h₁ : p → α) (h₂ : q → α) : α :=
  if hq : q then h₂ hq else h₁ (h.resolve_right hq)

instance exists_prop_decidable {p} (P : p → Prop)
  [Decidable p] [∀ h, Decidable (P h)] : Decidable (∃ h, P h) :=
if h : p then
  decidable_of_decidable_of_iff ⟨fun h2 => ⟨h, h2⟩, fun ⟨_, h2⟩ => h2⟩
else isFalse fun ⟨h', _⟩ => h h'

instance forall_prop_decidable {p} (P : p → Prop)
  [Decidable p] [∀ h, Decidable (P h)] : Decidable (∀ h, P h) :=
if h : p then
  decidable_of_decidable_of_iff ⟨fun h2 _ => h2, fun al => al h⟩
else isTrue fun h2 => absurd h2 h

/-! ## miscellaneous -/

theorem Bool.ff_ne_tt : false ≠ true := fun.

theorem Bool.eq_false_or_eq_true : (b : Bool) → b = true ∨ b = false
  | true => .inl rfl
  | false => .inr rfl

@[simp] theorem if_true {h : Decidable True} (t e : α) : ite True t e = t := if_pos trivial

@[simp] theorem if_false {h : Decidable False} (t e : α) : ite False t e = e := if_neg id

/-! ## Boolean order classes -/

/-- `TotalBLE le` asserts that `le` has a total order, that is, `le a b ∨ le b a`. -/
class TotalBLE (le : α → α → Bool) : Prop where
  /-- `le` is total: either `le a b` or `le b a`. -/
  total : le a b ∨ le b a

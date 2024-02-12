/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad, Floris van Doorn, Mario Carneiro
-/
import Std.Tactic.ByCases

/-! ## misc -/

attribute [simp] inline

/-! ## not -/

theorem Not.intro {a : Prop} (h : a → False) : ¬a := h

theorem Not.imp {a b : Prop} (H2 : ¬b) (H1 : a → b) : ¬a := mt H1 H2

/-- Ex falso for negation. From `¬a` and `a` anything follows. This is the same as `absurd` with
the arguments flipped, but it is in the `not` namespace so that projection notation can be used. -/
def Not.elim {α : Sort _} (H1 : ¬a) (H2 : a) : α := absurd H2 H1

theorem not_congr (h : a ↔ b) : ¬a ↔ ¬b := ⟨mt h.2, mt h.1⟩

/-! ## iff -/

-- This is needed for `calc` to work with `iff`.
instance : Trans Iff Iff Iff where
  trans p q := p.trans q

@[simp] theorem eq_iff_iff {p q : Prop} : (p = q) ↔ (p ↔ q) :=
  Iff.intro (fun e => Iff.intro e.mp e.mpr) propext

theorem iff_of_true (ha : a) (hb : b) : a ↔ b := by simp [ha, hb]
theorem iff_of_false (ha : ¬a) (hb : ¬b) : a ↔ b := by simp [ha, hb]
theorem iff_true_intro (h : a) : a ↔ True := by simp [h]
theorem iff_false_intro (h : ¬a) : a ↔ False := by simp [h]
theorem not_iff_false_intro (h : a) : ¬a ↔ False := by simp [h]

theorem iff_true_left  (ha : a) : (a ↔ b) ↔ b := by simp [iff_true_intro ha]
theorem iff_true_right (ha : a) : (b ↔ a) ↔ b := by simp [iff_true_intro ha]

theorem iff_false_left  (ha : ¬a) : (a ↔ b) ↔ ¬b := by simp [iff_false_intro ha]
theorem iff_false_right (ha : ¬a) : (b ↔ a) ↔ ¬b := by simp [iff_false_intro ha]

theorem eq_comm {a b : α} : a = b ↔ b = a := ⟨Eq.symm, Eq.symm⟩

/-# implies -/

@[simp] theorem imp_self : (a → a) ↔ True := iff_true_intro id

/--
This seems sensible as a simp rule, but in combination with `and_imp`, turns
`(a ∧ b) → False` into `a → b → False` which then leads to either `a -> ¬b`
or `¬(a ∧ b)` as normal forms.
-/
theorem imp_false : (a → False) ↔ ¬a := Iff.rfl

theorem imp.swap : (a → b → c) ↔ (b → a → c) := ⟨flip, flip⟩

theorem imp_not_comm : (a → ¬b) ↔ (b → ¬a) := imp.swap

/-! ## and -/

theorem And.imp (f : a → c) (g : b → d) (h : a ∧ b) : c ∧ d := ⟨f h.1, g h.2⟩

theorem And.imp_left (h : a → b) : a ∧ c → b ∧ c := .imp h id

theorem And.imp_right (h : a → b) : c ∧ a → c ∧ b := .imp id h

theorem and_iff_left_of_imp (h : a → b) : (a ∧ b) ↔ a :=
  ⟨And.left, fun ha => ⟨ha, h ha⟩⟩

theorem and_iff_right_of_imp (h : b → a) : (a ∧ b) ↔ b :=
  ⟨And.right, fun hb => ⟨h hb, hb⟩⟩

theorem and_iff_left (hb : b) : a ∧ b ↔ a := and_iff_left_of_imp fun _ => hb

theorem and_iff_right (ha : a) : a ∧ b ↔ b := and_iff_right_of_imp fun _ => ha

@[simp] theorem and_iff_left_iff_imp : ((a ∧ b) ↔ a) ↔ (a → b) :=
  ⟨fun h ha => (h.2 ha).2, and_iff_left_of_imp⟩

@[simp] theorem and_iff_right_iff_imp : ((a ∧ b) ↔ b) ↔ (b → a) :=
  ⟨fun h ha => (h.2 ha).1, and_iff_right_of_imp⟩


@[simp] theorem and_self_left : a ∧ (a ∧ b) ↔ a ∧ b :=
  ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, h.1, h.2⟩⟩

@[simp] theorem and_self_right : (a ∧ b) ∧ b ↔ a ∧ b :=
  ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, h.2⟩, h.2⟩⟩

theorem And.symm : a ∧ b → b ∧ a | ⟨ha, hb⟩ => ⟨hb, ha⟩

theorem And.assoc : (a ∧ b) ∧ c ↔ a ∧ (b ∧ c) :=
  ⟨fun ⟨⟨ha, hb⟩, hc⟩ => ⟨ha, hb, hc⟩, fun ⟨ha, hb, hc⟩ => ⟨⟨ha, hb⟩, hc⟩⟩

theorem And.left_comm : a ∧ (b ∧ c) ↔ b ∧ (a ∧ c) := by
  rw [← And.assoc, ← And.assoc, @And.comm a b]
  exact Iff.rfl

theorem And.right_comm : (a ∧ b) ∧ c ↔ (a ∧ c) ∧ b := by
  simp only [And.left_comm, And.comm]

theorem and_assoc : (a ∧ b) ∧ c ↔ a ∧ (b ∧ c) := And.assoc
theorem and_comm : a ∧ b ↔ b ∧ a := And.comm

theorem and_left_comm : a ∧ (b ∧ c) ↔ b ∧ (a ∧ c) := And.left_comm
theorem and_right_comm : (a ∧ b) ∧ c ↔ (a ∧ c) ∧ b := And.right_comm

theorem and_rotate : a ∧ b ∧ c ↔ b ∧ c ∧ a := by
  simp only [and_left_comm, And.comm]

@[simp] theorem and_not_self : ¬(a ∧ ¬a) | ⟨ha, hn⟩ => hn ha
@[simp] theorem not_and_self : ¬(¬a ∧ a) | ⟨hn, ha⟩ => hn ha

theorem and_congr_right (h : a → (b ↔ c)) : a ∧ b ↔ a ∧ c :=
⟨fun ⟨ha, hb⟩ => ⟨ha, (h ha).1 hb⟩, fun ⟨ha, hb⟩ => ⟨ha, (h ha).2 hb⟩⟩

theorem and_congr_left (h : c → (a ↔ b)) : a ∧ c ↔ b ∧ c :=
  and_comm.trans <| (and_congr_right h).trans and_comm

/- ### and lemmas to deprecate? -/

theorem and_congr (h₁ : a ↔ c) (h₂ : b ↔ d) : a ∧ b ↔ c ∧ d :=
  ⟨And.imp h₁.1 h₂.1, And.imp h₁.2 h₂.2⟩

theorem and_not_self_iff (a : Prop) : a ∧ ¬a ↔ False := iff_false_intro and_not_self
theorem not_and_self_iff (a : Prop) : ¬a ∧ a ↔ False := iff_false_intro not_and_self

/-! ## or -/

theorem not_not_em (a : Prop) : ¬¬(a ∨ ¬a) := fun h => h (.inr (h ∘ .inl))

-- TODO: rename or_self to or_self_eq
theorem or_self_iff : a ∨ a ↔ a := or_self _ ▸ .rfl

theorem Or.symm : a ∨ b → b ∨ a := .rec .inr .inl

theorem Or.imp (f : a → c) (g : b → d) (h : a ∨ b) : c ∨ d := h.elim (inl ∘ f) (inr ∘ g)

theorem Or.imp_left (f : a → b) : a ∨ c → b ∨ c := .imp f id

theorem Or.imp_right (f : b → c) : a ∨ b → a ∨ c := .imp id f

theorem Or.assoc : (a ∨ b) ∨ c ↔ a ∨ (b ∨ c) :=
  Iff.intro (.rec (.imp_right .inl) (.inr ∘ .inr)) (.rec (.inl ∘ .inl) (.imp_left .inr))

theorem Or.comm : a ∨ b ↔ b ∨ a := ⟨Or.symm, Or.symm⟩

--aliases
theorem or_assoc : (a ∨ b) ∨ c ↔ a ∨ (b ∨ c) := Or.assoc
theorem or_comm : a ∨ b ↔ b ∨ a := Or.comm

theorem or_left_comm {a b c : Prop} : a ∨ (b ∨ c) ↔ b ∨ (a ∨ c) := by
  rw [← or_assoc, ← or_assoc, @or_comm a b]
  exact Iff.rfl

theorem or_right_comm {a b c : Prop} : (a ∨ b) ∨ c ↔ (a ∨ c) ∨ b := by
  rw [or_assoc, or_assoc, @or_comm b]
  exact Iff.rfl

theorem Or.resolve_left {a b : Prop} (h: a ∨ b) (na : ¬a) : b := h.elim (absurd · na) id
theorem Or.resolve_right {a b : Prop} (h: a ∨ b) (nb : ¬b) : a := h.elim id (absurd · nb)
theorem Or.neg_resolve_left (h : ¬a ∨ b) (ha : a) : b := h.elim (absurd ha) id
theorem Or.neg_resolve_right (h : a ∨ ¬b) (nb : b) : a := h.elim id (absurd nb)

theorem or_iff_right_of_imp (ha : a → b) : (a ∨ b) ↔ b := ⟨Or.rec ha id, .inr⟩

theorem or_iff_left_of_imp (hb : b → a) : (a ∨ b) ↔ a := ⟨Or.rec id hb, .inl⟩

theorem not_or_intro {a b : Prop} (ha : ¬a) (hb : ¬b) : ¬(a ∨ b) := (·.elim ha hb)

@[simp] theorem or_iff_left_iff_imp : (a ∨ b ↔ a) ↔ (b → a) :=
  ⟨fun h hb => h.1 (Or.inr hb), or_iff_left_of_imp⟩

@[simp] theorem or_iff_right_iff_imp : (a ∨ b ↔ b) ↔ (a → b) := by
  rw [or_comm, or_iff_left_iff_imp]
  exact Iff.rfl

theorem or_congr (h₁ : a ↔ c) (h₂ : b ↔ d) : (a ∨ b) ↔ (c ∨ d) := ⟨.imp h₁.1 h₂.1, .imp h₁.2 h₂.2⟩
theorem or_congr_left (h : a ↔ b) : a ∨ c ↔ b ∨ c := or_congr h .rfl
theorem or_congr_right (h : b ↔ c) : a ∨ b ↔ a ∨ c := or_congr .rfl h

theorem or_iff_left (hb : ¬b) : a ∨ b ↔ a := by simp only [hb, or_false]
theorem or_iff_right (ha : ¬a) : a ∨ b ↔ b :=  by simp only [ha, false_or]
theorem or_rotate : a ∨ b ∨ c ↔ b ∨ c ∨ a := by simp only [or_left_comm, Or.comm]

/-! ## distributivity -/

theorem not_imp_of_and_not : a ∧ ¬b → ¬(a → b)
  | ⟨ha, hb⟩, h => hb <| h ha

theorem imp_and {α} : (α → b ∧ c) ↔ (α → b) ∧ (α → c) :=
  ⟨fun h => ⟨fun ha => (h ha).1, fun ha => (h ha).2⟩, fun h ha => ⟨h.1 ha, h.2 ha⟩⟩

@[simp] theorem and_imp : (a ∧ b → c) ↔ (a → b → c) :=
  ⟨fun h ha hb => h ⟨ha, hb⟩, fun h ⟨ha, hb⟩ => h ha hb⟩

/--
See `Decidable.not_and_iff_or_not` for the simplification rule that uses disjunction.
-/
theorem not_and : ¬(a ∧ b) ↔ (a → ¬b) := and_imp
theorem not_and' : ¬(a ∧ b) ↔ (b → ¬a) := not_and.trans imp_not_comm

/-- `∧` distributes over `∨` (on the left). -/
theorem and_or_left : a ∧ (b ∨ c) ↔ (a ∧ b) ∨ (a ∧ c) :=
  ⟨fun ⟨ha, hbc⟩ => hbc.imp (.intro ha) (.intro ha), Or.rec (.imp_right .inl) (.imp_right .inr)⟩

/-- `∧` distributes over `∨` (on the right). -/
theorem or_and_right : (a ∨ b) ∧ c ↔ (a ∧ c) ∨ (b ∧ c) := by
  simp [and_comm, and_or_left]

/-- `∨` distributes over `∧` (on the left). -/
theorem or_and_left : a ∨ (b ∧ c) ↔ (a ∨ b) ∧ (a ∨ c) :=
  ⟨Or.rec (fun ha => ⟨.inl ha, .inl ha⟩) (.imp .inr .inr),
   And.rec <| .rec (fun _ => .inl ·) (.imp_right ∘ .intro)⟩

/-- `∨` distributes over `∧` (on the right). -/
theorem and_or_right : (a ∧ b) ∨ c ↔ (a ∨ c) ∧ (b ∨ c) := by
  simp [or_comm, or_and_left]

theorem or_imp : (a ∨ b → c) ↔ (a → c) ∧ (b → c) :=
  ⟨fun h => ⟨h ∘ .inl, h ∘ .inr⟩, fun ⟨ha, hb⟩ => Or.rec ha hb⟩

theorem not_or : ¬(p ∨ q) ↔ ¬p ∧ ¬q := or_imp

theorem not_and_of_not_or_not (h : ¬a ∨ ¬b) : ¬(a ∧ b) := h.elim (mt (·.1)) (mt (·.2))

-- Idempotence rules that help normalize expressions with AC reordering
@[simp] theorem or_self_left : a ∨ (a ∨ b) ↔ a ∨ b := ⟨.rec .inl id, .rec .inl (.inr ∘ .inr)⟩
@[simp] theorem or_self_right : (a ∨ b) ∨ b ↔ a ∨ b :=
  Iff.intro (Or.rec id .inr) (Or.rec (fun ah => .inl (.inl ah)) .inr)


/-! ## exists and forall -/

section quantifiers
variable {p q : α → Prop} {b : Prop}


@[simp] theorem forall_exists_index {q : (∃ x, p x) → Prop} :
    (∀ h, q h) ↔ ∀ x (h : p x), q ⟨x, h⟩ :=
  ⟨fun h x hpx => h ⟨x, hpx⟩, fun h ⟨x, hpx⟩ => h x hpx⟩

theorem Exists.imp (h : ∀ a, p a → q a) : (∃ a, p a) → ∃ a, q a
  | ⟨a, hp⟩ => ⟨a, h a hp⟩

theorem exists_imp : ((∃ x, p x) → b) ↔ ∀ x, p x → b := forall_exists_index

@[simp] theorem exists_false : ¬(∃ _a : α, False) := fun ⟨_, h⟩ => h

@[simp] theorem exists_const (α) [i : Nonempty α] : (∃ _ : α, b) ↔ b :=
  ⟨fun ⟨_, h⟩ => h, i.elim Exists.intro⟩

theorem exists_congr (h : ∀ a, p a ↔ q a) : (∃ a, p a) ↔ ∃ a, q a :=
  ⟨Exists.imp fun x => (h x).1, Exists.imp fun x => (h x).2⟩

@[simp] theorem not_exists : (¬∃ x, p x) ↔ ∀ x, ¬p x := exists_imp

theorem forall_and : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) :=
  ⟨fun h => ⟨fun x => (h x).1, fun x => (h x).2⟩, fun ⟨h₁, h₂⟩ x => ⟨h₁ x, h₂ x⟩⟩

theorem exists_or : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ ∃ x, q x :=
  ⟨fun | ⟨x, .inl h⟩ => .inl ⟨x, h⟩ | ⟨x, .inr h⟩ => .inr ⟨x, h⟩,
   fun | .inl ⟨x, h⟩ => ⟨x, .inl h⟩ | .inr ⟨x, h⟩ => ⟨x, .inr h⟩⟩

@[simp] theorem forall_const (α : Sort _) [i : Nonempty α] : (α → b) ↔ b :=
  ⟨i.elim, fun hb _ => hb⟩

/-- Extract an element from a existential statement, using `Classical.choose`. -/
-- This enables projection notation.
@[reducible] noncomputable def Exists.choose (P : ∃ a, p a) : α := Classical.choose P

/-- Show that an element extracted from `P : ∃ a, p a` using `P.choose` satisfies `p`. -/
theorem Exists.choose_spec {p : α → Prop} (P : ∃ a, p a) : p P.choose := Classical.choose_spec P

@[simp] theorem forall_eq {p : α → Prop} {a' : α} : (∀ a, a = a' → p a) ↔ p a' :=
  ⟨fun h => h a' rfl, fun h _ e => e.symm ▸ h⟩

@[simp] theorem forall_eq' {a' : α} : (∀ a, a' = a → p a) ↔ p a' := by simp [@eq_comm _ a']


@[simp] theorem exists_eq : ∃ a, a = a' := ⟨_, rfl⟩

@[simp] theorem exists_eq' : ∃ a, a' = a := ⟨_, rfl⟩

@[simp] theorem exists_eq_left : (∃ a, a = a' ∧ p a) ↔ p a' :=
  ⟨fun ⟨_, e, h⟩ => e ▸ h, fun h => ⟨_, rfl, h⟩⟩

@[simp] theorem exists_eq_right : (∃ a, p a ∧ a = a') ↔ p a' :=
  (exists_congr <| by exact fun a => And.comm).trans exists_eq_left

@[simp] theorem exists_and_left : (∃ x, b ∧ p x) ↔ b ∧ (∃ x, p x) :=
  ⟨fun ⟨x, h, hp⟩ => ⟨h, x, hp⟩, fun ⟨h, x, hp⟩ => ⟨x, h, hp⟩⟩

@[simp] theorem exists_and_right : (∃ x, p x ∧ b) ↔ (∃ x, p x) ∧ b := by simp [And.comm]

@[simp] theorem exists_prop : (∃ _h : a, b) ↔ a ∧ b :=
  ⟨fun ⟨hp, hq⟩ => ⟨hp, hq⟩, fun ⟨hp, hq⟩ => ⟨hp, hq⟩⟩

@[simp] theorem exists_eq_left' : (∃ a, a' = a ∧ p a) ↔ p a' := by simp [@eq_comm _ a']

-- this theorem is needed to simplify the output of `List.mem_cons_iff`
@[simp] theorem forall_eq_or_imp : (∀ a, a = a' ∨ q a → p a) ↔ p a' ∧ ∀ a, q a → p a := by
  simp only [or_imp, forall_and, forall_eq]

@[simp] theorem exists_eq_or_imp : (∃ a, (a = a' ∨ q a) ∧ p a) ↔ p a' ∨ ∃ a, q a ∧ p a := by
  simp only [or_and_right, exists_or, exists_eq_left]

theorem forall_prop_of_true {p : Prop} {q : p → Prop} (h : p) : (∀ h' : p, q h') ↔ q h :=
  @forall_const (q h) p ⟨h⟩

theorem forall_prop_of_false {p : Prop} {q : p → Prop} (hn : ¬p) : (∀ h' : p, q h') ↔ True :=
  iff_true_intro fun h => hn.elim h

@[simp] theorem forall_apply_eq_imp_iff₂ {f : α → β} {p : α → Prop} {q : β → Prop} :
    (∀ b a, p a → f a = b → q b) ↔ ∀ a, p a → q (f a) :=
  ⟨fun h a ha => h (f a) a ha rfl, fun h _ a ha hb => hb ▸ h a ha⟩

end quantifiers

/-! ## decidable -/

/-- This will replace decide_not -/
@[simp]
theorem decide_not2 (p : Prop) [h : Decidable (p → False)] [g : Decidable p] :
    (@decide (¬p) h) = !(@decide p g) := by
    have eq : h = instDecidableNot := Subsingleton.elim h instDecidableNot
    apply Eq.trans (congrArg (@decide _) eq)
    cases g <;> rfl

@[simp] theorem Decidable.not_not [Decidable p] : ¬¬p ↔ p := ⟨of_not_not, not_not_intro⟩

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

/-- Iff version of decide_eq_true_eq-/
theorem decide_eq_true_iff (p : Prop) [Decidable p] : (decide p = true) ↔ p := by simp

@[simp]
theorem decide_eq_false_iff_not (p : Prop) {_ : Decidable p} : (decide p = false) ↔ ¬p :=
  ⟨of_decide_eq_false, decide_eq_false⟩

@[simp]
theorem decide_eq_decide {p q : Prop} {_ : Decidable p} {_ : Decidable q} :
    decide p = decide q ↔ (p ↔ q) := by
  apply Iff.intro
  · intro h
    rw [← decide_eq_true_iff p, h, decide_eq_true_iff]
    exact Iff.rfl
  · intro h
    simp [h]

theorem Decidable.or_iff_not_imp_left [h : Decidable a] : a ∨ b ↔ (¬a → b) := by
  by_cases g : a <;> simp [g]

theorem Decidable.or_iff_not_imp_right [inst : Decidable b] : a ∨ b ↔ (¬b → a) := by
  by_cases g : b <;> simp [g]

theorem Decidable.of_not_imp [Decidable a] (h : ¬(a → b)) : a := by
  by_cases g : a <;> simp [g] at *

--  576
theorem Decidable.not_imp_not [Decidable a] : (¬a → ¬b) ↔ (b → a) :=
  ⟨fun h hb => byContradiction (h · hb), mt⟩

theorem Decidable.not_or_of_imp [Decidable a] (h : a → b) : ¬a ∨ b :=
  if ha : a then .inr (h ha) else .inl ha

theorem Decidable.imp_iff_not_or [Decidable a] : (a → b) ↔ (¬a ∨ b) :=
  ⟨not_or_of_imp, Or.neg_resolve_left⟩


-- 603
theorem Decidable.not_iff_not [Decidable a] [Decidable b] : (¬a ↔ ¬b) ↔ (a ↔ b) := by
  by_cases g : a <;> simp [g]


theorem Decidable.imp_iff_or_not [Decidable b] : b → a ↔ a ∨ ¬b :=
  Decidable.imp_iff_not_or.trans or_comm

theorem Decidable.not_imp_iff_and_not [Decidable a] : ¬(a → b) ↔ a ∧ ¬b := by
  by_cases g : a <;> simp [g]

theorem Decidable.iff_iff_and_or_not_and_not {a b : Prop} [Decidable b] :
    (a ↔ b) ↔ (a ∧ b) ∨ (¬a ∧ ¬b) :=
  ⟨fun e => if h : b then .inl ⟨e.2 h, h⟩ else .inr ⟨mt e.1 h, h⟩,
   Or.rec (And.rec iff_of_true) (And.rec iff_of_false)⟩

theorem Decidable.iff_iff_not_or_and_or_not [Decidable a] [Decidable b] :
    (a ↔ b) ↔ (¬a ∨ b) ∧ (a ∨ ¬b) := by
  rw [iff_iff_implies_and_implies a b]; simp only [imp_iff_not_or, Or.comm]

theorem Decidable.not_and_iff_or_not_not [Decidable a] : ¬(a ∧ b) ↔ ¬a ∨ ¬b :=
  ⟨fun h => if ha : a then .inr (h ⟨ha, ·⟩) else .inl ha, not_and_of_not_or_not⟩

theorem Decidable.not_and_iff_or_not_not' [Decidable b] : ¬(a ∧ b) ↔ ¬a ∨ ¬b :=
  ⟨fun h => if hb : b then .inl (h ⟨·, hb⟩) else .inr hb, not_and_of_not_or_not⟩

/-- Transfer decidability of `a` to decidability of `b`, if the propositions are equivalent.
**Important**: this function should be used instead of `rw` on `decidable b`, because the
kernel will get stuck reducing the usage of `propext` otherwise,
and `dec_trivial` will not work. -/
@[inline] def decidable_of_iff (a : Prop) (h : a ↔ b) [Decidable a] : Decidable b :=
  decidable_of_decidable_of_iff h

/-- Transfer decidability of `b` to decidability of `a`, if the propositions are equivalent.
This is the same as `decidable_of_iff` but the iff is flipped. -/
@[inline] def decidable_of_iff' (b : Prop) (h : a ↔ b) [Decidable b] : Decidable a :=
  decidable_of_decidable_of_iff h.symm

instance Decidable.predToBool (p : α → Prop) [DecidablePred p] :
    CoeDep (α → Prop) p (α → Bool) := ⟨fun b => decide <| p b⟩

-- These lemmas are pulled from Mathlib

@[simp]
theorem if_true_left_eq_or (p : Prop) [Decidable p] (f : Prop) :
    ite p True f ↔ p ∨ f := by by_cases h : p <;> simp [h]

@[simp]
theorem if_false_left_eq_and (p : Prop) [Decidable p] (f : Prop) :
    ite p False f ↔ ¬p ∧ f := by by_cases h : p <;> simp [h]

@[simp]
theorem if_true_right_eq_or (p : Prop) [Decidable p] (t : Prop) :
    ite p t True ↔ ¬p ∨ t := by by_cases h : p <;> simp [h]

@[simp]
theorem if_false_right_eq_and (p : Prop) [Decidable p] (t : Prop) :
    ite p t False ↔ p ∧ t := by by_cases h : p <;> simp [h]

/-! ## if-then-else -/

/-- Negation of the condition `P : Prop` in a `dite` is the same as swapping the branches. -/
@[simp] theorem dite_not (P : Prop) {_ : Decidable P}  (x : ¬P → α) (y : ¬¬P → α) :
    dite (¬P) x y = dite P (fun h => y (not_not_intro h)) x := by
  by_cases h : P <;> simp [h]

/-- Negation of the condition `P : Prop` in a `ite` is the same as swapping the branches. -/
@[simp] theorem ite_not (P : Prop) {_ : Decidable P} (x y : α) : ite (¬P) x y = ite P y x :=
  dite_not P (fun _ => x) (fun _ => y)

@[simp] theorem dite_eq_left_iff {P : Prop} [Decidable P] {B : ¬ P → α} :
    dite P (fun _ => a) B = a ↔ ∀ h, B h = a := by
  by_cases P <;> simp [*, forall_prop_of_true, forall_prop_of_false]

@[simp] theorem dite_eq_right_iff {P : Prop} [Decidable P] {A : P → α} :
    (dite P A fun _ => b) = b ↔ ∀ (h : P), A h = b := by
  by_cases P <;> simp [*, forall_prop_of_true, forall_prop_of_false]

@[simp] theorem ite_eq_left_iff {P : Prop} [Decidable P] : ite P a b = a ↔ ¬P → b = a :=
  dite_eq_left_iff

@[simp] theorem ite_eq_right_iff {P : Prop} [Decidable P] : ite P a b = b ↔ P → a = b :=
  dite_eq_right_iff

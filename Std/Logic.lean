/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad, Floris van Doorn, Mario Carneiro
-/
import Std.Base.Logic
import Std.Tactic.Init
import Std.Tactic.NoMatch
import Std.Tactic.Alias
import Std.Tactic.Lint.Misc
import Std.Tactic.ByCases

instance {f : α → β} [DecidablePred p] : DecidablePred (p ∘ f) :=
  inferInstanceAs <| DecidablePred fun x => p (f x)

theorem Function.comp_def {α β δ} (f : β → δ) (g : α → β) : f ∘ g = fun x => f (g x) := rfl

/-! ## not -/

theorem not_not_not : ¬¬¬a ↔ ¬a := ⟨mt not_not_intro, not_not_intro⟩

theorem not_not_of_not_imp : ¬(a → b) → ¬¬a := mt Not.elim

theorem not_of_not_imp {a : Prop} : ¬(a → b) → ¬b := mt fun h _ => h

@[simp] theorem imp_not_self : (a → ¬a) ↔ ¬a := ⟨fun h ha => h ha ha, fun h _ => h⟩

/-! ## iff -/

-- This is needed for `calc` to work with `iff`.
instance : Trans Iff Iff Iff where
  trans p q := p.trans q

theorem iff_def : (a ↔ b) ↔ (a → b) ∧ (b → a) := iff_iff_implies_and_implies ..

theorem iff_def' : (a ↔ b) ↔ (b → a) ∧ (a → b) := iff_def.trans And.comm

/-- Non-dependent eliminator for `Iff`. -/
def Iff.elim (f : (a → b) → (b → a) → α) (h : a ↔ b) : α := f h.1 h.2

theorem Eq.to_iff : a = b → (a ↔ b) | rfl => Iff.rfl

theorem iff_of_eq : a = b → (a ↔ b) := Eq.to_iff

theorem neq_of_not_iff : ¬(a ↔ b) → a ≠ b := mt Eq.to_iff

theorem iff_iff_eq : (a ↔ b) ↔ a = b := ⟨propext, iff_of_eq⟩

theorem of_iff_true (h : a ↔ True) : a := h.2 ⟨⟩

theorem not_of_iff_false : (a ↔ False) → ¬a := Iff.mp

theorem iff_congr (h₁ : a ↔ c) (h₂ : b ↔ d) : (a ↔ b) ↔ (c ↔ d) :=
  ⟨fun h => h₁.symm.trans <| h.trans h₂, fun h => h₁.trans <| h.trans h₂.symm⟩

theorem not_true : (¬True) ↔ False := iff_false_intro (not_not_intro ⟨⟩)

theorem not_false_iff : (¬False) ↔ True := iff_true_intro not_false

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

/-! ## implies -/

@[nolint unusedArguments]
theorem imp_intro {α β : Prop} (h : α) : β → α := fun _ => h

theorem imp_imp_imp {a b c d : Prop} (h₀ : c → a) (h₁ : b → d) : (a → b) → (c → d) := (h₁ ∘ · ∘ h₀)

theorem imp_iff_right {a : Prop} (ha : a) : (a → b) ↔ b := ⟨fun f => f ha, imp_intro⟩

-- This is not marked `@[simp]` because we have `implies_true : (α → True) = True` in core.
theorem imp_true_iff (α : Sort u) : (α → True) ↔ True := iff_true_intro fun _ => trivial

theorem false_imp_iff (a : Prop) : (False → a) ↔ True := iff_true_intro False.elim

theorem true_imp_iff (α : Prop) : (True → α) ↔ α := ⟨fun h => h trivial, fun h _ => h⟩

theorem imp_congr_left (h : a ↔ b) : (a → c) ↔ (b → c) :=
  ⟨fun hac ha => hac (h.2 ha), fun hbc ha => hbc (h.1 ha)⟩

theorem imp_congr_right (h : a → (b ↔ c)) : (a → b) ↔ (a → c) :=
  ⟨fun hab ha => (h ha).1 (hab ha), fun hcd ha => (h ha).2 (hcd ha)⟩

theorem imp_congr_ctx (h₁ : a ↔ c) (h₂ : c → (b ↔ d)) : (a → b) ↔ (c → d) :=
  (imp_congr_left h₁).trans (imp_congr_right h₂)

theorem imp_congr (h₁ : a ↔ c) (h₂ : b ↔ d) : (a → b) ↔ (c → d) := imp_congr_ctx h₁ fun _ => h₂

theorem imp_iff_not (hb : ¬b) : a → b ↔ ¬a := imp_congr_right fun _ => iff_false_intro hb

/-! ## and -/

/-- Non-dependent eliminator for `And`. -/
abbrev And.elim (f : a → b → α) (h : a ∧ b) : α := f h.1 h.2

-- TODO: rename and_self to and_self_eq
theorem and_self_iff : a ∧ a ↔ a := and_self _ ▸ .rfl

theorem and_congr_left' (h : a ↔ b) : a ∧ c ↔ b ∧ c := and_congr h .rfl

theorem and_congr_right' (h : b ↔ c) : a ∧ b ↔ a ∧ c := and_congr .rfl h

theorem and_congr_right_eq (h : a → b = c) : (a ∧ b) = (a ∧ c) :=
  propext <| and_congr_right fun hc => h hc ▸ .rfl

theorem and_congr_left_eq (h : c → a = b) : (a ∧ c) = (b ∧ c) :=
  propext <| and_congr_left fun hc => h hc ▸ .rfl

theorem and_and_and_comm : (a ∧ b) ∧ c ∧ d ↔ (a ∧ c) ∧ b ∧ d := by
  rw [← and_assoc, @and_right_comm a, and_assoc]

theorem and_and_left : a ∧ b ∧ c ↔ (a ∧ b) ∧ a ∧ c := by
  rw [and_and_and_comm, and_self]

theorem and_and_right : (a ∧ b) ∧ c ↔ (a ∧ c) ∧ b ∧ c := by
  rw [and_and_and_comm, and_self]

@[simp] theorem iff_self_and : (p ↔ p ∧ q) ↔ (p → q) := by
  rw [@Iff.comm p, and_iff_left_iff_imp]

@[simp] theorem iff_and_self : (p ↔ q ∧ p) ↔ (p → q) := by rw [and_comm, iff_self_and]

@[simp] theorem and_congr_right_iff : (a ∧ b ↔ a ∧ c) ↔ (a → (b ↔ c)) :=
  ⟨fun h ha => by simp [ha] at h; exact h, and_congr_right⟩

@[simp] theorem and_congr_left_iff : (a ∧ c ↔ b ∧ c) ↔ c → (a ↔ b) := by
  simp only [and_comm, ← and_congr_right_iff]

theorem not_and_of_not_left (b : Prop) : ¬a → ¬(a ∧ b) := mt And.left

theorem not_and_of_not_right (a : Prop) {b : Prop} : ¬b → ¬(a ∧ b) := mt And.right

/- ## or -/

theorem or_or_or_comm : (a ∨ b) ∨ c ∨ d ↔ (a ∨ c) ∨ b ∨ d := by
  rw [← or_assoc, @or_right_comm a, or_assoc]

theorem or_or_distrib_left : a ∨ b ∨ c ↔ (a ∨ b) ∨ a ∨ c := by rw [or_or_or_comm, or_self]

theorem or_or_distrib_right : (a ∨ b) ∨ c ↔ (a ∨ c) ∨ b ∨ c := by rw [or_or_or_comm, or_self]

/-! ## exists and forall -/

section quantifiers
variable {p q : α → Prop} {b : Prop}

theorem forall_imp (h : ∀ a, p a → q a) : (∀ a, p a) → ∀ a, q a :=
fun h' a => h a (h' a)

theorem Exists.imp' {β} {q : β → Prop} (f : α → β) (hpq : ∀ a, p a → q (f a)) :
    (∃ a, p a) → ∃ b, q b
  | ⟨_, hp⟩ => ⟨_, hpq _ hp⟩

section forall_congr

-- Port note: this is `forall_congr` from Lean 3. In Lean 4, there is already something
-- with that name and a slightly different type.
theorem forall_congr' (h : ∀ a, p a ↔ q a) : (∀ a, p a) ↔ ∀ a, q a :=
  ⟨fun H a => (h a).1 (H a), fun H a => (h a).2 (H a)⟩

variable {β : α → Sort _}
theorem forall₂_congr {p q : ∀ a, β a → Prop} (h : ∀ a b, p a b ↔ q a b) :
    (∀ a b, p a b) ↔ ∀ a b, q a b :=
  forall_congr' fun a => forall_congr' <| h a

theorem exists₂_congr {p q : ∀ a, β a → Prop} (h : ∀ a b, p a b ↔ q a b) :
    (∃ a b, p a b) ↔ ∃ a b, q a b :=
  exists_congr fun a => exists_congr <| h a

variable {γ : ∀ a, β a → Sort _}
theorem forall₃_congr {p q : ∀ a b, γ a b → Prop} (h : ∀ a b c, p a b c ↔ q a b c) :
    (∀ a b c, p a b c) ↔ ∀ a b c, q a b c :=
  forall_congr' fun a => forall₂_congr <| h a

theorem exists₃_congr {p q : ∀ a b, γ a b → Prop} (h : ∀ a b c, p a b c ↔ q a b c) :
    (∃ a b c, p a b c) ↔ ∃ a b c, q a b c :=
  exists_congr fun a => exists₂_congr <| h a

variable {δ : ∀ a b, γ a b → Sort _}
theorem forall₄_congr {p q : ∀ a b c, δ a b c → Prop} (h : ∀ a b c d, p a b c d ↔ q a b c d) :
    (∀ a b c d, p a b c d) ↔ ∀ a b c d, q a b c d :=
  forall_congr' fun a => forall₃_congr <| h a

theorem exists₄_congr {p q : ∀ a b c, δ a b c → Prop} (h : ∀ a b c d, p a b c d ↔ q a b c d) :
    (∃ a b c d, p a b c d) ↔ ∃ a b c d, q a b c d :=
  exists_congr fun a => exists₃_congr <| h a

variable {ε : ∀ a b c, δ a b c → Sort _}
theorem forall₅_congr {p q : ∀ a b c d, ε a b c d → Prop}
    (h : ∀ a b c d e, p a b c d e ↔ q a b c d e) :
    (∀ a b c d e, p a b c d e) ↔ ∀ a b c d e, q a b c d e :=
  forall_congr' fun a => forall₄_congr <| h a

theorem exists₅_congr {p q : ∀ a b c d, ε a b c d → Prop}
    (h : ∀ a b c d e, p a b c d e ↔ q a b c d e) :
    (∃ a b c d e, p a b c d e) ↔ ∃ a b c d e, q a b c d e :=
  exists_congr fun a => exists₄_congr <| h a

end forall_congr

alias ⟨forall_not_of_not_exists, not_exists_of_forall_not⟩ := not_exists

theorem Exists.nonempty : (∃ x, p x) → Nonempty α | ⟨x, _⟩ => ⟨x⟩

theorem not_forall_of_exists_not {p : α → Prop} : (∃ x, ¬p x) → ¬∀ x, p x
  | ⟨x, hn⟩, h => hn (h x)

@[simp] theorem exists_eq_right_right : (∃ (a : α), p a ∧ q a ∧ a = a') ↔ p a' ∧ q a' := by
  simp [← and_assoc]

@[simp] theorem exists_eq_right_right' : (∃ (a : α), p a ∧ q a ∧ a' = a) ↔ p a' ∧ q a' := by
  (conv in _=_ => rw [eq_comm]); simp

@[simp] theorem exists_apply_eq_apply (f : α → β) (a' : α) : ∃ a, f a = f a' := ⟨a', rfl⟩

theorem forall_comm {p : α → β → Prop} : (∀ a b, p a b) ↔ (∀ b a, p a b) :=
  ⟨fun h b a => h a b, fun h a b => h b a⟩

theorem exists_comm {p : α → β → Prop} : (∃ a b, p a b) ↔ (∃ b a, p a b) :=
  ⟨fun ⟨a, b, h⟩ => ⟨b, a, h⟩, fun ⟨b, a, h⟩ => ⟨a, b, h⟩⟩

@[simp] theorem forall_apply_eq_imp_iff {f : α → β} {p : β → Prop} :
    (∀ b a, f a = b → p b) ↔ ∀ a, p (f a) := by simp [forall_comm]

@[simp] theorem forall_eq_apply_imp_iff {f : α → β} {p : β → Prop} :
    (∀ b a, b = f a → p b) ↔ ∀ a, p (f a) := by simp [forall_comm]

end quantifiers

/-! ## decidable -/

theorem Decidable.by_contra [Decidable p] : (¬p → False) → p := of_not_not

/-- Construct a non-Prop by cases on an `Or`, when the left conjunct is decidable. -/
protected def Or.by_cases [Decidable p] {α : Sort u} (h : p ∨ q) (h₁ : p → α) (h₂ : q → α) : α :=
  if hp : p then h₁ hp else h₂ (h.resolve_left hp)

/-- Construct a non-Prop by cases on an `Or`, when the right conjunct is decidable. -/
protected def Or.by_cases' [Decidable q] {α : Sort u} (h : p ∨ q) (h₁ : p → α) (h₂ : q → α) : α :=
  if hq : q then h₂ hq else h₁ (h.resolve_right hq)

theorem Decidable.not_imp_symm [Decidable a] (h : ¬a → b) (hb : ¬b) : a :=
  byContradiction <| hb ∘ h

theorem Decidable.not_imp_comm [Decidable a] [Decidable b] : (¬a → b) ↔ (¬b → a) :=
  ⟨not_imp_symm, not_imp_symm⟩

theorem Decidable.not_imp_self [Decidable a] : (¬a → a) ↔ a := by
  have := @imp_not_self (¬a); rwa [not_not] at this

theorem Decidable.imp_or [Decidable a] : (a → b ∨ c) ↔ (a → b) ∨ (a → c) := by
  by_cases a <;> simp_all

theorem Decidable.imp_or' [Decidable b] : (a → b ∨ c) ↔ (a → b) ∨ (a → c) :=
  if h : b then by simp [h] else by
    rw [eq_false h, false_or]; exact (or_iff_right_of_imp fun hx x => (hx x).elim).symm

theorem Decidable.peirce (a b : Prop) [Decidable a] : ((a → b) → a) → a :=
  if ha : a then fun _ => ha else fun h => h ha.elim

theorem peirce' {a : Prop} (H : ∀ b : Prop, (a → b) → a) : a := H _ id

theorem Decidable.not_iff_comm [Decidable a] [Decidable b] : (¬a ↔ b) ↔ (¬b ↔ a) := by
  rw [@iff_def (¬a), @iff_def (¬b)]; exact and_congr not_imp_comm imp_not_comm

theorem Decidable.not_iff [Decidable b] : ¬(a ↔ b) ↔ (¬a ↔ b) := by
  by_cases h : b <;> simp [h, iff_true, iff_false]

theorem Decidable.iff_not_comm [Decidable a] [Decidable b] : (a ↔ ¬b) ↔ (b ↔ ¬a) := by
  rw [@iff_def a, @iff_def b]; exact and_congr imp_not_comm not_imp_comm

theorem Decidable.not_and_not_right [Decidable b] : ¬(a ∧ ¬b) ↔ (a → b) :=
  ⟨fun h ha => not_imp_symm (And.intro ha) h, fun h ⟨ha, hb⟩ => hb <| h ha⟩

theorem Decidable.or_iff_not_and_not [Decidable a] [Decidable b] : a ∨ b ↔ ¬(¬a ∧ ¬b) := by
  rw [← not_or, not_not]

theorem Decidable.and_iff_not_or_not [Decidable a] [Decidable b] : a ∧ b ↔ ¬(¬a ∨ ¬b) := by
  rw [← not_and_iff_or_not_not, not_not]

theorem Decidable.imp_iff_right_iff [Decidable a] : (a → b ↔ b) ↔ a ∨ b :=
  ⟨fun H => (Decidable.em a).imp_right fun ha' => H.1 fun ha => (ha' ha).elim,
   fun H => H.elim imp_iff_right fun hb => iff_of_true (fun _ => hb) hb⟩

theorem Decidable.and_or_imp [Decidable a] : a ∧ b ∨ (a → c) ↔ a → b ∨ c :=
  if ha : a then by simp only [ha, true_and, true_imp_iff]
  else by simp only [ha, false_or, false_and, false_imp_iff]

theorem Decidable.or_congr_left' [Decidable c] (h : ¬c → (a ↔ b)) : a ∨ c ↔ b ∨ c := by
  rw [or_iff_not_imp_right, or_iff_not_imp_right]; exact imp_congr_right h

theorem Decidable.or_congr_right' [Decidable a] (h : ¬a → (b ↔ c)) : a ∨ b ↔ a ∨ c := by
  rw [or_iff_not_imp_left, or_iff_not_imp_left]; exact imp_congr_right h

/-- Prove that `a` is decidable by constructing a boolean `b` and a proof that `b ↔ a`.
(This is sometimes taken as an alternate definition of decidability.) -/
def decidable_of_bool : ∀ (b : Bool), (b ↔ a) → Decidable a
  | true, h => isTrue (h.1 rfl)
  | false, h => isFalse (mt h.2 Bool.noConfusion)

protected theorem Decidable.not_forall {p : α → Prop} [Decidable (∃ x, ¬p x)]
    [∀ x, Decidable (p x)] : (¬∀ x, p x) ↔ ∃ x, ¬p x :=
  ⟨Decidable.not_imp_symm fun nx x => Decidable.not_imp_symm (fun h => ⟨x, h⟩) nx,
   not_forall_of_exists_not⟩

protected alias ⟨Decidable.exists_not_of_not_forall, _⟩ := Decidable.not_forall

protected theorem Decidable.not_forall_not {p : α → Prop} [Decidable (∃ x, p x)] :
    (¬∀ x, ¬p x) ↔ ∃ x, p x :=
  (@Decidable.not_iff_comm _ _ _ (decidable_of_iff (¬∃ x, p x) not_exists)).1 not_exists

protected theorem Decidable.not_exists_not {p : α → Prop} [∀ x, Decidable (p x)] :
    (¬∃ x, ¬p x) ↔ ∀ x, p x := by
  simp only [not_exists, Decidable.not_not]

/-! ## classical logic -/

namespace Classical

/-- The Double Negation Theorem: `¬¬P` is equivalent to `P`.
The left-to-right direction, double negation elimination (DNE),
is classically true but not constructively. -/
@[scoped simp] theorem not_not : ¬¬a ↔ a := Decidable.not_not

theorem not_forall {p : α → Prop} : (¬∀ x, p x) ↔ ∃ x, ¬p x :=
  Decidable.not_forall

alias ⟨exists_not_of_not_forall, _⟩ := not_forall

theorem not_forall_not {p : α → Prop} : (¬∀ x, ¬p x) ↔ ∃ x, p x := Decidable.not_forall_not

theorem not_exists_not {p : α → Prop} : (¬∃ x, ¬p x) ↔ ∀ x, p x := Decidable.not_exists_not

theorem forall_or_exists_not (P : α → Prop) : (∀ a, P a) ∨ ∃ a, ¬ P a := by
  rw [← not_forall]; exact em _

theorem exists_or_forall_not (P : α → Prop) : (∃ a, P a) ∨ ∀ a, ¬ P a := by
  rw [← not_exists]; exact em _

theorem or_iff_not_imp_left : a ∨ b ↔ (¬a → b) :=
  Decidable.or_iff_not_imp_left

theorem or_iff_not_imp_right : a ∨ b ↔ (¬b → a) :=
  Decidable.or_iff_not_imp_right

theorem not_imp_iff_and_not : ¬(a → b) ↔ a ∧ ¬b :=
  Decidable.not_imp_iff_and_not

theorem not_and_iff_or_not_not : ¬(a ∧ b) ↔ ¬a ∨ ¬b :=
  Decidable.not_and_iff_or_not_not

theorem not_iff : ¬(a ↔ b) ↔ (¬a ↔ b) :=
  Decidable.not_iff

end Classical

/-! ## equality -/

theorem heq_iff_eq : HEq a b ↔ a = b := ⟨eq_of_heq, heq_of_eq⟩

theorem proof_irrel_heq {p q : Prop} (hp : p) (hq : q) : HEq hp hq := by
  cases propext (iff_of_true hp hq); rfl

@[simp] theorem eq_rec_constant {α : Sort _} {a a' : α} {β : Sort _} (y : β) (h : a = a') :
    (@Eq.rec α a (fun α _ => β) y a' h) = y := by cases h; rfl

theorem congrArg₂ (f : α → β → γ) {x x' : α} {y y' : β}
    (hx : x = x') (hy : y = y') : f x y = f x' y' := by subst hx hy; rfl

theorem congrFun₂ {β : α → Sort _} {γ : ∀ a, β a → Sort _}
    {f g : ∀ a b, γ a b} (h : f = g) (a : α) (b : β a) :
    f a b = g a b :=
  congrFun (congrFun h _) _

theorem congrFun₃ {β : α → Sort _} {γ : ∀ a, β a → Sort _} {δ : ∀ a b, γ a b → Sort _}
      {f g : ∀ a b c, δ a b c} (h : f = g) (a : α) (b : β a) (c : γ a b) :
    f a b c = g a b c :=
  congrFun₂ (congrFun h _) _ _

theorem funext₂ {β : α → Sort _} {γ : ∀ a, β a → Sort _}
    {f g : ∀ a b, γ a b} (h : ∀ a b, f a b = g a b) : f = g :=
  funext fun _ => funext <| h _

theorem funext₃ {β : α → Sort _} {γ : ∀ a, β a → Sort _} {δ : ∀ a b, γ a b → Sort _}
    {f g : ∀ a b c, δ a b c} (h : ∀ a b c, f a b c = g a b c) : f = g :=
  funext fun _ => funext₂ <| h _

theorem ne_of_apply_ne {α β : Sort _} (f : α → β) {x y : α} : f x ≠ f y → x ≠ y :=
  mt <| congrArg _

protected theorem Eq.congr (h₁ : x₁ = y₁) (h₂ : x₂ = y₂) : x₁ = x₂ ↔ y₁ = y₂ := by
  subst h₁; subst h₂; rfl

theorem Eq.congr_left {x y z : α} (h : x = y) : x = z ↔ y = z := by rw [h]

theorem Eq.congr_right {x y z : α} (h : x = y) : z = x ↔ z = y := by rw [h]

alias congr_arg := congrArg
alias congr_arg₂ := congrArg₂
alias congr_fun := congrFun
alias congr_fun₂ := congrFun₂
alias congr_fun₃ := congrFun₃

theorem eq_mp_eq_cast (h : α = β) : Eq.mp h = cast h :=
  rfl

theorem eq_mpr_eq_cast (h : α = β) : Eq.mpr h = cast h.symm :=
  rfl

@[simp] theorem cast_cast : ∀ (ha : α = β) (hb : β = γ) (a : α),
    cast hb (cast ha a) = cast (ha.trans hb) a
  | rfl, rfl, _ => rfl

theorem heq_of_cast_eq : ∀ (e : α = β) (_ : cast e a = a'), HEq a a'
  | rfl, rfl => .rfl

theorem cast_eq_iff_heq : cast e a = a' ↔ HEq a a' :=
  ⟨heq_of_cast_eq _, fun h => by cases h; rfl⟩

theorem eqRec_eq_cast {α : Sort _} {a : α} {motive : (a' : α) → a = a' → Sort _}
    (x : motive a (rfl : a = a)) {a' : α} (e : a = a') :
    @Eq.rec α a motive x a' e = cast (e ▸ rfl) x := by
  subst e; rfl

--Porting note: new theorem. More general version of `eqRec_heq`
theorem eqRec_heq_self {α : Sort _} {a : α} {motive : (a' : α) → a = a' → Sort _}
    (x : motive a (rfl : a = a)) {a' : α} (e : a = a') :
    HEq (@Eq.rec α a motive x a' e) x := by
  subst e; rfl

@[simp]
theorem eqRec_heq_iff_heq {α : Sort _} {a : α} {motive : (a' : α) → a = a' → Sort _}
    (x : motive a (rfl : a = a)) {a' : α} (e : a = a') {β : Sort _} (y : β) :
    HEq (@Eq.rec α a motive x a' e) y ↔ HEq x y := by
  subst e; rfl

@[simp]
theorem heq_eqRec_iff_heq {α : Sort _} {a : α} {motive : (a' : α) → a = a' → Sort _}
    (x : motive a (rfl : a = a)) {a' : α} (e : a = a') {β : Sort _} (y : β) :
    HEq y (@Eq.rec α a motive x a' e) ↔ HEq y x := by
  subst e; rfl

/-! ## membership -/

section Mem
variable [Membership α β] {s t : β} {a b : α}

theorem ne_of_mem_of_not_mem (h : a ∈ s) : b ∉ s → a ≠ b := mt fun e => e ▸ h

theorem ne_of_mem_of_not_mem' (h : a ∈ s) : a ∉ t → s ≠ t := mt fun e => e ▸ h

end Mem

/-! ## if-then-else -/

@[simp] theorem if_true {h : Decidable True} (t e : α) : ite True t e = t := if_pos trivial

@[simp] theorem if_false {h : Decidable False} (t e : α) : ite False t e = e := if_neg id

theorem ite_id [Decidable c] {α} (t : α) : (if c then t else t) = t := by split <;> rfl

/-- A function applied to a `dite` is a `dite` of that function applied to each of the branches. -/
theorem apply_dite (f : α → β) (P : Prop) [Decidable P] (x : P → α) (y : ¬P → α) :
    f (dite P x y) = dite P (fun h => f (x h)) (fun h => f (y h)) := by
  by_cases h : P <;> simp [h]

/-- A function applied to a `ite` is a `ite` of that function applied to each of the branches. -/
theorem apply_ite (f : α → β) (P : Prop) [Decidable P] (x y : α) :
    f (ite P x y) = ite P (f x) (f y) :=
  apply_dite f P (fun _ => x) (fun _ => y)

/-- A `dite` whose results do not actually depend on the condition may be reduced to an `ite`. -/
@[simp] theorem dite_eq_ite [Decidable P] : (dite P (fun _ => a) fun _ => b) = ite P a b := rfl

/-! ## miscellaneous -/

/-- Ex falso, the nondependent eliminator for the `Empty` type. -/
def Empty.elim : Empty → C := fun.

instance : Subsingleton Empty := ⟨fun a => a.elim⟩

instance : DecidableEq Empty := fun a => a.elim

/-- Ex falso, the nondependent eliminator for the `PEmpty` type. -/
def PEmpty.elim : PEmpty → C := fun.

instance : Subsingleton PEmpty := ⟨fun a => a.elim⟩

instance : DecidableEq PEmpty := fun a => a.elim

@[simp] theorem not_nonempty_empty : ¬Nonempty Empty := fun ⟨h⟩ => h.elim

@[simp] theorem not_nonempty_pempty : ¬Nonempty PEmpty := fun ⟨h⟩ => h.elim

instance [Subsingleton α] [Subsingleton β] : Subsingleton (α × β) :=
  ⟨fun {..} {..} => by congr <;> apply Subsingleton.elim⟩

instance : Inhabited (Sort _) := ⟨PUnit⟩

instance : Inhabited default := ⟨PUnit.unit⟩

instance {α β} [Inhabited α] : Inhabited (PSum α β) := ⟨PSum.inl default⟩

instance {α β} [Inhabited β] : Inhabited (PSum α β) := ⟨PSum.inr default⟩

-- TODO(Mario): profile first, this is a dangerous instance
-- instance (priority := 10) {α} [Subsingleton α] : DecidableEq α
--   | a, b => isTrue (Subsingleton.elim a b)

-- @[simp] -- TODO(Mario): profile
theorem eq_iff_true_of_subsingleton [Subsingleton α] (x y : α) : x = y ↔ True :=
  iff_true_intro (Subsingleton.elim ..)

/-- If all points are equal to a given point `x`, then `α` is a subsingleton. -/
theorem subsingleton_of_forall_eq (x : α) (h : ∀ y, y = x) : Subsingleton α :=
  ⟨fun a b => h a ▸ h b ▸ rfl⟩

theorem subsingleton_iff_forall_eq (x : α) : Subsingleton α ↔ ∀ y, y = x :=
  ⟨fun _ y => Subsingleton.elim y x, subsingleton_of_forall_eq x⟩

example [Subsingleton α] (p : α → Prop) : Subsingleton (Subtype p) :=
  ⟨fun ⟨x, _⟩ ⟨y, _⟩ => by congr; exact Subsingleton.elim x y⟩

theorem false_ne_true : False ≠ True := fun h => h.symm ▸ trivial

theorem Bool.eq_iff_iff {a b : Bool} : a = b ↔ (a ↔ b) := by cases b <;> simp

theorem ne_comm {α} {a b : α} : a ≠ b ↔ b ≠ a := ⟨Ne.symm, Ne.symm⟩

theorem congr_eqRec {β : α → Sort _} (f : (x : α) → β x → γ) (h : x = x') (y : β x) :
  f x' (Eq.rec y h) = f x y := by cases h; rfl

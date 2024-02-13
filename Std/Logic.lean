/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad, Floris van Doorn, Mario Carneiro
-/
import Std.Tactic.Init
import Std.Tactic.Alias
import Std.Tactic.Lint.Misc

instance {f : α → β} [DecidablePred p] : DecidablePred (p ∘ f) :=
  inferInstanceAs <| DecidablePred fun x => p (f x)

/-! ## exists and forall -/

alias ⟨forall_not_of_not_exists, not_exists_of_forall_not⟩ := not_exists

/-! ## decidable -/

protected alias ⟨Decidable.exists_not_of_not_forall, _⟩ := Decidable.not_forall

/-! ## classical logic -/

namespace Classical

alias ⟨exists_not_of_not_forall, _⟩ := not_forall

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
    (dite P A fun _ => b) = b ↔ ∀ h, A h = b := by
  by_cases P <;> simp [*, forall_prop_of_true, forall_prop_of_false]

@[simp] theorem ite_eq_left_iff {P : Prop} [Decidable P] : ite P a b = a ↔ ¬P → b = a :=
  dite_eq_left_iff

@[simp] theorem ite_eq_right_iff {P : Prop} [Decidable P] : ite P a b = b ↔ P → a = b :=
  dite_eq_right_iff

/-- A `dite` whose results do not actually depend on the condition may be reduced to an `ite`. -/
@[simp] theorem dite_eq_ite [Decidable P] : (dite P (fun _ => a) fun _ => b) = ite P a b := rfl

-- We don't mark this as `simp` as it is already handled by `ite_eq_right_iff`.
theorem ite_some_none_eq_none [Decidable P] :
    (if P then some x else none) = none ↔ ¬ P := by
  simp only [ite_eq_right_iff]

@[simp] theorem ite_some_none_eq_some [Decidable P] :
    (if P then some x else none) = some y ↔ P ∧ x = y := by
  split <;> simp_all

/-! ## miscellaneous -/

instance : DecidableEq PEmpty := fun a => a.elim

@[simp] theorem not_nonempty_empty  : ¬Nonempty Empty := fun ⟨h⟩ => h.elim
@[simp] theorem not_nonempty_pempty : ¬Nonempty PEmpty := fun ⟨h⟩ => h.elim

instance [Subsingleton α] [Subsingleton β] : Subsingleton (α × β) :=
  ⟨fun {..} {..} => by congr <;> apply Subsingleton.elim⟩

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

theorem ne_comm {α} {a b : α} : a ≠ b ↔ b ≠ a := ⟨Ne.symm, Ne.symm⟩

theorem congr_eqRec {β : α → Sort _} (f : (x : α) → β x → γ) (h : x = x') (y : β x) :
  f x' (Eq.rec y h) = f x y := by cases h; rfl

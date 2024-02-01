/-
Copyright (c) 2023 F. G. Dorais. No rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad, F. G. Dorais
-/

namespace Bool

instance (p : Bool → Prop) [inst : DecidablePred p] : Decidable (∀ x, p x) :=
  match inst true, inst false with
  | isFalse ht, _ => isFalse fun h => absurd (h _) ht
  | _, isFalse hf => isFalse fun h => absurd (h _) hf
  | isTrue ht, isTrue hf => isTrue fun | true => ht | false => hf

instance (p : Bool → Prop) [inst : DecidablePred p] : Decidable (∃ x, p x) :=
  match inst true, inst false with
  | isTrue ht, _ => isTrue ⟨_, ht⟩
  | _, isTrue hf => isTrue ⟨_, hf⟩
  | isFalse ht, isFalse hf => isFalse fun | ⟨true, h⟩ => absurd h ht | ⟨false, h⟩ => absurd h hf

@[simp] theorem and_not_self : ∀ (x : Bool), (x && !x) = false := by decide
@[simp] theorem not_and_self : ∀ (x : Bool), (!x && x) = false := by decide

@[simp] theorem and_self_left (a b : Bool) : (a && (a && b)) = (a && b) := by revert a b ; decide
@[simp] theorem and_self_right (a b : Bool) : ((a && b) && b) = (a && b) := by revert a b ; decide

@[simp] theorem not_or_self : ∀ (x : Bool), (!x || x) = true := by decide
@[simp] theorem or_not_self : ∀ (x : Bool), (x || !x) = true := by decide

@[simp] theorem or_self_left (a b : Bool) : (a || (a || b)) = (a || b) := by revert a b ; decide
@[simp] theorem or_self_right (a b : Bool) : ((a || b) || b) = (a || b) := by revert a b ; decide

@[simp] theorem not_beq_self : ∀ (x : Bool), (!x == x) = false := by decide
@[simp] theorem beq_not_self : ∀ (x : Bool), (x == !x) = false := by decide

@[simp] theorem beq_self_left (a b : Bool) : (a == (a == b)) = b := by revert a b ; decide
@[simp] theorem beq_self_right (a b : Bool) : ((a == b) == b) = a := by revert a b ; decide

@[simp] theorem not_bne_self : ∀ (x : Bool), (!x != x) = true := by decide
@[simp] theorem bne_not_self : ∀ (x : Bool), (x != !x) = true := by decide

@[simp] theorem bne_self_left (a b : Bool) : (a != (a != b)) = b := by revert a b ; decide
@[simp] theorem bne_self_right (a b : Bool) : ((a != b) != b) = a := by revert a b ; decide


/--
These two rules follow trivially by simp, but are needed to avoid non-termination
in false_eq and true_eq.
-/
@[simp] theorem false_eq_true : (false = true) = False := by simp
@[simp] theorem true_eq_false : (true = false) = False := by simp

-- The two lemmas below normalize terms with a constant to the right-hand
-- side but risk non-termination (false_eq_true and true_eq_false address this)
@[simp low] theorem false_eq (b : Bool) : (false = b) = (b = false) := by
  cases b <;> simp

@[simp low] theorem true_eq (b : Bool) : (true = b) = (b = true) := by
  cases b <;> simp

/- ## Simp lemmas for Bool to Prop normal forms: `b = true`, `b = false`-/
-- From mathlib: coe_iff_coe
@[simp]
theorem coe_true_iff_true : ∀(a b : Bool), (a ↔ b) ↔ a = b := by decide

@[simp]
theorem coe_true_iff_false : ∀(a b : Bool), (a ↔ b = false) ↔ a = (!b) := by decide

@[simp]
theorem coe_false_iff_true : ∀(a b : Bool), (a = false ↔ b) ↔ (!a) = b := by decide

@[simp]
theorem coe_false_iff_false : ∀(a b : Bool), (a = false ↔ b = false) ↔ (!a) = (!b) := by decide

/-# beq -/

@[simp] theorem true_beq  (b : Bool) : (true  == b) =  b := by cases b <;> simp [BEq.beq]
@[simp] theorem false_beq (b : Bool) : (false == b) = !b := by cases b <;> simp [BEq.beq]
@[simp] theorem beq_true  (b : Bool) : (b == true)  =  b := by cases b <;> simp [BEq.beq]
@[simp] theorem beq_false (b : Bool) : (b == false) = !b := by cases b <;> simp [BEq.beq]

@[simp] theorem true_bne  (b : Bool) : (true  != b) = !b := by cases b <;> simp [BEq.beq]
@[simp] theorem false_bne (b : Bool) : (false != b) =  b := by cases b <;> simp [BEq.beq]
@[simp] theorem bne_true  (b : Bool) : (b != true)  = !b := by cases b <;> simp [BEq.beq]
@[simp] theorem bne_false (b : Bool) : (b != false) =  b := by cases b <;> simp [BEq.beq]

/-# bool to prop normal forms: b = true, b = false -/

@[simp] theorem or_eq_false  (b c : Bool) : ((b || c) = false) = ¬(b ∨ c) := by
  cases b <;> simp

@[simp] theorem beq_eq_false  (b c : Bool) : ((b == c) = false) = ¬(b = c) := by
  cases b <;> simp

@[simp] theorem bne_eq_false  (b c : Bool) : ((b != c) = false) = (b = c) := by
  cases b <;> simp

-- Note. We push coercions to atoms so we can reduce the need for reasoning
-- about mixed Prop/Bool formulas.  As part of this, there are simp lemmas
-- that automatically distribute (_ = true) and (_ = false) over operations
-- because `(_ = true)` is introduced implicitly when coericing a `Bool` to a
-- `Prop` and `(_ = false)` arrises from `simp` rules on negation.

@[simp] theorem ite_eq_true_distrib (p : Prop) [Decidable p] (t f : Bool) :
    (ite p t f = true) = ite p (t = true) (f = true) := by
  by_cases h : p <;> simp [h]

@[simp] theorem ite_eq_false_distrib (p : Prop) [Decidable p] (t f : Bool) :
    (ite p t f = false) = ite p (t = false) (f = false) := by
  by_cases h : p <;> simp [h]

@[simp] theorem cond_eq_true_distrib (c t f : Bool) :
    (cond c t f = true) = ite (c = true) (t = true) (f = true) := by
  cases c <;> simp

@[simp] theorem cond_eq_false_distrib (c t f : Bool) :
    (cond c t f = false) = ite (c = true) (t = false) (f = false) := by
  cases c <;> simp

/-# misc -/

@[simp] theorem not_beq (b c : Bool) : (!(b == c)) = (b != c) := by
  cases b <;> cases c <;> simp

@[simp] theorem not_bne (b c : Bool) : (!(b != c)) = (b == c) := by
  cases b <;> cases c <;> simp

@[simp] theorem iff_eq_eq (b c : Bool) :
    ((b = true) ↔ (c = true)) = (b = c) := by
  cases b <;> cases c <;> simp

@[simp]
theorem decide_eq (b c : Bool) : decide (b = c) = (b == c) := by
  cases b <;> cases c <;> simp

/-# ite -/

@[simp]
theorem if_true_left_eq_or  (p : Prop) [Decidable p] (f : Bool) :
    (ite p true f) = (p || f) := by by_cases h : p <;> simp [h]

@[simp]
theorem if_false_left_eq_and  (p : Prop) [Decidable p] (f : Bool) :
    (ite p false f) = (!p && f) := by by_cases h : p <;> simp [h]

@[simp]
theorem if_true_right_eq_or  (p : Prop) [Decidable p] (t : Bool) :
    (ite p t true) = (!(p : Bool) || t) := by by_cases h : p <;> simp [h]

@[simp]
theorem if_false_right_eq_and  (p : Prop) [Decidable p] (t : Bool) :
    (ite p t false) = (p && t) := by by_cases h : p <;> simp [h]

/-
`not_if_prop_coerce_true` and `not_if_prop_coerce_false` are new
rules motivated by coercions distributing over ite and some
interactions with other lemmas.

We want to simplify this term
1. if u then b else c ≠ true

It can reduces to
2. ¬(if u then b else c = true)

This could get simplified to:

3. (if u then b else c) = false

But it also goes to:
4. ¬(if u then b = true else c = true)

So we normalize to
5. if u then b = false else c = false
-/

@[simp]
theorem not_if_prop_coerce_true (p : Prop) [Decidable p] (b c : Bool) :
  ¬(if p then b = true else c = true) ↔ (if p then b = false else c = false) := by
  by_cases h : p <;> simp [h]

@[simp]
theorem not_if_prop_coerce_false (p : Prop) [Decidable p] (b c : Bool) :
  ¬(if p then b = false else c = false) ↔ (if p then b = true else c = true) := by
  by_cases h : p <;> simp [h]

/-# cond -/
@[simp]
theorem cond_true_left_eq_or    (c f : Bool) : (cond c true f) = (c || f) := by cases c <;> simp

@[simp]
theorem cond_false_left_eq_and  (c f : Bool) : (cond c false f) = (!c && f) := by cases c <;> simp

@[simp]
theorem cond_true_right_eq_or   (c t : Bool) : (cond c t true) = (!c || t) := by cases c <;> simp

@[simp]
theorem cond_false_right_eq_and (c t : Bool) : (cond c t false) = (c && t) := by cases c <;> simp

@[simp]
theorem cond_not (c t f : Bool) : cond (!c) t f = cond c f t := by cases c <;> simp

@[simp]
theorem cond_same (c b : Bool) : cond c b b = b := by cases c <;> simp

@[simp]
theorem cond_true_same (c b : Bool) : cond c c b = (c || b) := by cases c <;> simp

@[simp]
theorem cond_false_same (c b : Bool) : cond c b c = (c && b) := by cases c <;> simp

-- !b : Prop reduces to `b = false`, so this normalized that.
@[simp] theorem and_eq_false_iff_not_and (b c : Bool) : (b && c) = false ↔ ¬(b ∧ c) := by
  cases b <;> simp

@[simp]
protected theorem decide_eq_true (b : Bool) : decide (b = true) = b := by
  cases b <;> simp

@[simp]
protected theorem decide_eq_false (b : Bool) : decide (b = false) = !b := by
  cases b <;> simp

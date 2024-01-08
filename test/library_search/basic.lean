import Std
set_option autoImplicit true

-- Enable this option for tracing:
-- set_option trace.Tactic.stdLibrarySearch true
-- And this option to trace all candidate lemmas before application.
-- set_option trace.Tactic.stdLibrarySearch.lemmas true

noncomputable section

/-- info: Try this: exact Nat.lt.base x -/
#guard_msgs in
example (x : Nat) : x ≠ x.succ := Nat.ne_of_lt (by std_apply?)

/-- info: Try this: exact Nat.zero_lt_succ 1 -/
#guard_msgs in
example : 0 ≠ 1 + 1 := Nat.ne_of_lt (by std_apply?)

example : 0 ≠ 1 + 1 := Nat.ne_of_lt (by exact Fin.size_pos')

/-- info: Try this: exact Nat.add_comm x y -/
#guard_msgs in
example (x y : Nat) : x + y = y + x := by std_apply?

/-- info: Try this: exact fun a => Nat.add_le_add_right a k -/
#guard_msgs in
example (n m k : Nat) : n ≤ m → n + k ≤ m + k := by std_apply?

/-- info: Try this: exact Nat.mul_dvd_mul_left a w -/
#guard_msgs in
example (ha : a > 0) (w : b ∣ c) : a * b ∣ a * c := by std_apply?

-- Could be any number of results (`Int.one`, `Int.zero`, etc)
#guard_msgs (drop info) in
example : Int := by std_apply?

/-- info: Try this: Nat.lt.base x -/
#guard_msgs in
example : x < x + 1 := exact?%

/-- info: Try this: exact p -/
#guard_msgs in
example (P : Prop) (p : P) : P := by std_apply?
/-- info: Try this: exact False.elim (np p) -/
#guard_msgs in
example (P : Prop) (p : P) (np : ¬P) : false := by std_apply?
/-- info: Try this: exact h x rfl -/
#guard_msgs in
example (X : Type) (P : Prop) (x : X) (h : ∀ x : X, x = x → P) : P := by std_apply?

-- Could be any number of results (`fun x => x`, `id`, etc)
#guard_msgs (drop info) in
example (α : Prop) : α → α := by std_apply?

-- Note: these examples no longer work after we turned off lemmas with discrimination key `#[*]`.
-- example (p : Prop) : (¬¬p) → p := by std_apply? -- says: `exact not_not.mp`
-- example (a b : Prop) (h : a ∧ b) : a := by std_apply? -- says: `exact h.left`
-- example (P Q : Prop) : (¬ Q → ¬ P) → (P → Q) := by std_apply? -- say: `exact Function.mtr`

/-- info: Try this: exact Nat.add_comm a b -/
#guard_msgs in
example (a b : Nat) : a + b = b + a :=
by std_apply?

/-- info: Try this: exact Nat.mul_sub_left_distrib n m k -/
#guard_msgs in
example (n m k : Nat) : n * (m - k) = n * m - n * k :=
by std_apply?

attribute [symm] Eq.symm

/-- info: Try this: exact Eq.symm (Nat.mul_sub_left_distrib n m k) -/
#guard_msgs in
example (n m k : Nat) : n * m - n * k = n * (m - k) := by
  std_apply?

/-- info: Try this: exact eq_comm -/
#guard_msgs in
example {α : Type} (x y : α) : x = y ↔ y = x := by std_apply?

/-- info: Try this: exact Nat.add_pos_left ha b -/
#guard_msgs in
example (a b : Nat) (ha : 0 < a) (_hb : 0 < b) : 0 < a + b := by std_apply?

/-- info: Try this: exact Nat.add_pos_left ha b -/
#guard_msgs in
-- Verify that if maxHeartbeats is 0 we don't stop immediately.
set_option maxHeartbeats 0 in
example (a b : Nat) (ha : 0 < a) (_hb : 0 < b) : 0 < a + b := by std_apply?

section synonym

/-- info: Try this: exact Nat.add_pos_left ha b -/
#guard_msgs in
example (a b : Nat) (ha : a > 0) (_hb : 0 < b) : 0 < a + b := by std_apply?

/-- info: Try this: exact Nat.le_of_dvd w h -/
#guard_msgs in
example (a b : Nat) (h : a ∣ b) (w : b > 0) : a ≤ b :=
by std_apply?

/-- info: Try this: exact Nat.le_of_dvd w h -/
#guard_msgs in
example (a b : Nat) (h : a ∣ b) (w : b > 0) : b ≥ a := by std_apply?

-- TODO: A lemma with head symbol `¬` can be used to prove `¬ p` or `⊥`
/-- info: Try this: exact Nat.not_lt_zero a -/
#guard_msgs in
example (a : Nat) : ¬ (a < 0) := by std_apply?
/-- info: Try this: exact Nat.not_succ_le_zero a h -/
#guard_msgs in
example (a : Nat) (h : a < 0) : False := by std_apply?

-- An inductive type hides the constructor's arguments enough
-- so that `apply?` doesn't accidentally close the goal.
inductive P : Nat → Prop
  | gt_in_head {n : Nat} : n < 0 → P n

-- This lemma with `>` as its head symbol should also be found for goals with head symbol `<`.
theorem lemma_with_gt_in_head (a : Nat) (h : P a) : 0 > a := by cases h; assumption

-- This lemma with `false` as its head symbols should also be found for goals with head symbol `¬`.
theorem lemma_with_false_in_head (a b : Nat) (_h1 : a < b) (h2 : P a) : False := by
  apply Nat.not_lt_zero; cases h2; assumption

/-- info: Try this: exact lemma_with_gt_in_head a h -/
#guard_msgs in
example (a : Nat) (h : P a) : 0 > a := by std_apply?
/-- info: Try this: exact lemma_with_gt_in_head a h -/
#guard_msgs in
example (a : Nat) (h : P a) : a < 0 := by std_apply?

/-- info: Try this: exact lemma_with_false_in_head a b h1 h2 -/
#guard_msgs in
example (a b : Nat) (h1 : a < b) (h2 : P a) : False := by std_apply?

-- TODO this no longer works:
-- example (a b : Nat) (h1 : a < b) : ¬ (P a) := by std_apply? -- says `exact lemma_with_false_in_head a b h1`

end synonym

/-- info: Try this: exact fun P => iff_not_self -/
#guard_msgs in
example : ∀ P : Prop, ¬(P ↔ ¬P) := by std_apply?

-- We even find `iff` results:
/-- info: Try this: exact Iff.mpr (Nat.dvd_add_iff_left h₁) h₂ -/
#guard_msgs in
example {a b c : Nat} (h₁ : a ∣ c) (h₂ : a ∣ b + c) : a ∣ b := by std_apply?

-- Note: these examples no longer work after we turned off lemmas with discrimination key `#[*]`.
-- example {α : Sort u} (h : Empty) : α := by std_apply? -- says `exact Empty.elim h`
-- example (f : A → C) (g : B → C) : (A ⊕ B) → C := by std_apply? -- says `exact Sum.elim f g`
-- example (n : Nat) (r : ℚ) : ℚ := by std_apply? using n, r -- exact nsmulRec n r

opaque f : Nat → Nat
axiom F (a b : Nat) : f a ≤ f b ↔ a ≤ b

/-- info: Try this: exact Iff.mpr (F a b) h -/
#guard_msgs in
example (a b : Nat) (h : a ≤ b) : f a ≤ f b := by std_apply?

/-- info: Try this: exact List.join L -/
#guard_msgs in
example (L : List (List Nat)) : List Nat := by std_apply? using L

-- Could be any number of results
#guard_msgs (drop info) in
example (P _Q : List Nat) (h : Nat) : List Nat := by std_apply? using h, P

-- Could be any number of results
#guard_msgs (drop info) in
example (l : List α) (f : α → β ⊕ γ) : List β × List γ := by
  std_apply? using f -- partitionMap f l

-- Could be any number of results (`Nat.mul n m`, `Nat.add n m`, etc)
#guard_msgs (drop info) in
example (n m : Nat) : Nat := by std_apply? using n, m

#guard_msgs (drop info) in
example (P Q : List Nat) (_h : Nat) : List Nat := by std_exact? using P, Q

-- Check that we don't use sorryAx:
-- (see https://github.com/leanprover-community/mathlib4/issues/226)
theorem Bool_eq_iff {A B : Bool} : (A = B) = (A ↔ B) :=
  by (cases A <;> cases B <;> simp)

/-- info: Try this: exact Bool_eq_iff -/
#guard_msgs in
theorem Bool_eq_iff2 {A B : Bool} : (A = B) = (A ↔ B) := by
  std_apply? -- exact Bool_eq_iff

-- Example from https://leanprover.zulipchat.com/#narrow/stream/287929-mathlib4/topic/library_search.20regression/near/354025788
-- Disabled for Std
--/-- info: Try this: exact surjective_quot_mk r -/
--#guard_msgs in
--example {r : α → α → Prop} : Function.Surjective (Quot.mk r) := by exact?

-- Example from https://leanprover.zulipchat.com/#narrow/stream/287929-mathlib4/topic/library_search.20failing.20to.20apply.20symm
-- Disabled for Std
-- /-- info: Try this: exact Iff.symm Nat.prime_iff -/
--#guard_msgs in
--example (n : Nat) : Prime n ↔ Nat.Prime n := by
--  std_exact?

-- Example from https://leanprover.zulipchat.com/#narrow/stream/287929-mathlib4/topic/exact.3F.20recent.20regression.3F/near/387691588
-- Disabled for Std
--lemma ex' (x : Nat) (_h₁ : x = 0) (h : 2 * 2 ∣ x) : 2 ∣ x := by
--  std_exact? says exact dvd_of_mul_left_dvd h

-- https://leanprover.zulipchat.com/#narrow/stream/287929-mathlib4/topic/apply.3F.20failure/near/402534407
-- Disabled for Std
--example (P Q : Prop) (h : P → Q) (h' : ¬Q) : ¬P := by
--  std_exact? says exact mt h h'

-- Removed until we come up with a way of handling nonspecific lemmas
-- that does not pollute the output or cause too much slow-down.
-- -- Example from https://leanprover.zulipchat.com/#narrow/stream/287929-mathlib4/topic/Exact.3F.20fails.20on.20le_antisymm/near/388993167
-- set_option linter.unreachableTactic false in
-- example {x y : ℝ} (hxy : x ≤ y) (hyx : y ≤ x) : x = y := by
--   -- This example non-deterministically picks between `le_antisymm hxy hyx` and `ge_antisymm hyx hxy`.
--   first
--   | exact? says exact le_antisymm hxy hyx
--   | exact? says exact ge_antisymm hyx hxy

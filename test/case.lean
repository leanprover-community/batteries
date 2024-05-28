import Batteries.Tactic.Case

set_option linter.missingDocs false

example (h : x = y) (h' : z = w) : x = y ∧ z = w := by
  constructor
  fail_if_success show z = z
  case _ : z = _
  · exact h'
  exact h

example (h : x = y) (h' : z = w) : x = y ∧ z = w := by
  constructor
  case _ : z = _ =>
    exact h'
  case left =>
    exact h

example (h : x = y) (h' : z = w) : x = y ∧ z = w := by
  constructor
  case _ : z = _ | left => assumption

example (h : x = y) (h' : z = w) : x = y ∧ z = w := by
  constructor
  case _ : _ | _ : _ => assumption

example (h : x = y) (h' : z = w) : x = y ∧ z = w := by
  constructor
  case left | _ : z = _ => assumption

example (h : x = y) (h' : z = w) : x = y ∧ z = w := by
  constructor
  case _ : z = _ => ?foo
  case foo := h'
  case left := h

example (h : x = y) (h' : z = w) : x = y ∧ z + 0 = w := by
  constructor
  case right : z = _ =>
    guard_target =ₛ z = w
    exact h'
  case _ : x = y := h

example (h : x = y) : x = y ∧ x = y := by
  constructor
  case _ : x = y | _ : x = y => ?foo
  -- Closes both
  case foo => exact h

example (h : x = y) : x = y ∧ x = y ∧ x = y := by
  refine ⟨?foo, ?_, ?_⟩
  · exact h
  case _ : x = y | _ : x = y => ?foo
  -- This metavariable was already assigned, so no more goals.

/--
error: 'case' tactic failed, value
  ?left
depends on the main goal metavariable '?left'
-/
#guard_msgs in
example : False ∧ True := by
  constructor
  case _ : False => ?left

/--
error: type mismatch
  ?right
has type
  True : Prop
but is expected to have type
  False : Prop
-/
#guard_msgs in
example : False ∧ True := by
  constructor
  case _ : False => ?right

/--
error: 'case' tactic failed, value
  ?right
depends on the main goal metavariable '?right'
-/
#guard_msgs in
example : False ∧ False := by
  constructor
  case left => ?right
  case right => ?left

example (h : x = y) (h' : z = w) : x = y ∧ z + 0 = w := by
  constructor
  case _ : z = _ =>
    guard_target =ₛ z = w
    exact h'
  case left =>
    exact h

example (x y z : α) (h : x = y) (h' : y = z) : x = z := by
  apply Eq.trans
  case _ : id α := y
  -- Note: `case` inserts a `let_fun` since `id α` and `α` aren't defeq with reducible transparency
  · guard_target =ₛ x = show id α from y
    exact h
  · guard_target = y = z
    exact h'

example (x y z : α) (h : x = y) (h' : y = z) : x = z := by
  apply Eq.trans
  case _ : α := y
  -- Note: `case` detects defeq with reducible transparency, so doesn't insert type hint
  · guard_target =ₛ x = y
    exact h
  · guard_target = y = z
    exact h'

def Injective (f : α → β) : Prop := ∀ ⦃a₁ a₂⦄, f a₁ = f a₂ → a₁ = a₂

theorem cancel_injective (h : Injective f) : f x = f y ↔ x = y := by
  refine ⟨fun e => h e, ?_⟩
  intro h
  cases h
  rfl

example (h : Injective f) (h' : f x = f y) : x = y := by
  rw [cancel_injective] at h'
  case _ : Injective f := h
  exact h'

example (h : Injective f) (h' : f x = f y) : x = y := by
  rw [cancel_injective] at h'
  case _ : Injective f
  · exact h
  exact h'

example (hf : Injective f) (hg : Injective g) (h : g (f x) = g (f y)) : x = y := by
  rw [cancel_injective, cancel_injective] at h
  case _ : Injective f | _ : Injective g => assumption
  exact h

example (hf : Injective f) (hg : Injective g) (h : g (f x) = g (f y)) : x = y := by
  rw [cancel_injective, cancel_injective] at h
  repeat case _ : Injective _ => assumption
  exact h

example (hf : Injective f) (hg : Injective g) (h : g (f x) = g (f y)) : x = y := by
  rw [cancel_injective, cancel_injective] at h
  case _ : Injective f | _ : Injective g
  · guard_target = Injective f
    assumption
  · guard_target = Injective g
    assumption
  exact h

example (hf : Injective f) (hg : Injective g) (h : g (f x) = g (f y)) : x = y := by
  rw [cancel_injective, cancel_injective] at h
  case _ : Injective f | _ : Injective g => _
  · guard_target = Injective f
    assumption
  · guard_target = Injective g
    assumption
  exact h

example (a : Nat) : 0 + a = a := by
  induction a
  case _ n ih : 0 + (n + 1) = n + 1 =>
    guard_target =ₛ 0 + (n + 1) = n + 1
    rw [← Nat.add_assoc, ih]
  case _ : 0 + 0 = 0 := rfl

example (a : Nat) : 0 + a = a := by
  induction a
  case _ n ih : 0 + (n + 1) = n + 1 | _ : 0 + 0 = 0
  · rw [← Nat.add_assoc, ih]
  · rfl

example : True ∧ ∀ x : Nat, x = x := by
  constructor
  case' _ : ∀ _, _ =>
    intro z
  case left => trivial
  guard_target =ₛ z = z
  rfl

-- Test focusing by full match, suffix match, and prefix match
/--
warning: unused variable `x`
note: this linter can be disabled with `set_option linter.unusedVariables false`
---
warning: unused variable `y`
note: this linter can be disabled with `set_option linter.unusedVariables false`
---
warning: unused variable `z`
note: this linter can be disabled with `set_option linter.unusedVariables false`
-/
#guard_msgs in
example : True := by
  have x : Bool := ?a
  have y : Nat := ?a.b.c
  have z : String := ?c.b.a
  case a : Bool := true
  case a : Nat := 0
  case a : String := ""
  trivial

-- Test priorities when focusing by full match, suffix match, and prefix match
example : True := by
  let x : Nat := ?a
  let y : Nat := ?c.b.a
  let z : Nat := ?c'.b.a
  let w : Nat := ?a.b.c
  case a : Nat := 0
  case a : Nat := 1
  case a : Nat := 2
  case a : Nat := 3
  guard_hyp x : Nat := 0
  guard_hyp y : Nat := 2
  guard_hyp z : Nat := 1
  guard_hyp w : Nat := 3
  trivial

-- Test renaming when not pattern matching
example (n : Nat) : 0 ≤ n := by
  induction n
  case _ : 0 ≤ 0 | succ n ih
  · guard_target =ₛ 0 ≤ 0
    constructor
  · guard_target =ₛ 0 ≤ n + 1
    guard_hyp ih : 0 ≤ n
    simp

import Batteries.Tactic.SqueezeScope

-- undo changes to simp set after test was written
attribute [-simp] Nat.add_left_cancel_iff Nat.add_right_cancel_iff

set_option linter.missingDocs false

/--
info: Try this:
  [apply] simp only [Nat.add_comm]
-/
#guard_msgs in
example : x + 1 = 1 + x := by simp? [Nat.add_comm, Nat.mul_comm]
/--
info: Try this:
  [apply] dsimp only [Nat.reduceAdd]
-/
#guard_msgs in
example : 1 + 1 = 2 := by dsimp?

@[simp] def bar (z : Nat) := 1 + z
@[simp] def baz (z : Nat) := 1 + z

@[simp] def foo : Nat → Nat → Nat
  | 0, z => bar z
  | _+1, z => baz z

/--
info: Try this:
  [apply] simp only [foo, bar]
---
info: Try this:
  [apply] simp only [foo, baz]
-/
#guard_msgs in
example : foo x y = 1 + y := by
  cases x <;> simp? -- two printouts:
  -- "Try this: simp only [foo, bar]"
  -- "Try this: simp only [foo, baz]"

/--
info: Try this:
  [apply] simp only [foo, bar, baz]
-/
#guard_msgs in
example : foo x y = 1 + y := by
  squeeze_scope
    cases x <;> simp -- only one printout: "Try this: simp only [foo, baz, bar]"

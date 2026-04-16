import Batteries.Tactic.Lint.TypeClass
import Lean.Elab.Command

open Batteries.Tactic.Lint

namespace A

-- The following two tests test both the `impossibleInstance` linter and also that the
-- `Lean.withDeclRef?` function (used in the implementation of the linter) makes the
-- linter's warning appear on the name of the declaration (if it has one) or the `instance` keyword,
-- instead of at the beginning of the declaration's docstring.
-- It does this by using `(positions := true)` in `guard_msgs`.
/--
@ +2:29...30
warning: unused variable `β`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
---
@ +2:15...25
warning: This instance has 1 argument that cannot be inferred using typeclass synthesis. Specifically

  argument 2: `{β : Type}`

These arguments are not instance-implicit and appear neither in another instance-implicit argument nor the return type, so they cannot be inferred using typeclass synthesis.

Note: This linter can be disabled with `set_option linter.impossibleInstance false`
-/
#guard_msgs (positions := true) in
/-- This is a doc string needed for testing the `withDeclRef` function. -/
local instance impossible {α β : Type} [Inhabited α] : Nonempty α := ⟨default⟩

-- Version of the above without a name (see comment above for why this exists).
/--
@ +2:18...19
warning: unused variable `β`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
---
@ +2:6...14
warning: This instance has 1 argument that cannot be inferred using typeclass synthesis. Specifically

  argument 2: `{β : Type}`

These arguments are not instance-implicit and appear neither in another instance-implicit argument nor the return type, so they cannot be inferred using typeclass synthesis.

Note: This linter can be disabled with `set_option linter.impossibleInstance false`
-/
#guard_msgs (positions := true) in
/-- This is a doc string needed for testing the `withDeclRef` function. -/
local instance {α β : Type} [Inhabited α] : Nonempty α := ⟨default⟩

run_meta guard (← impossibleInstance.test ``impossible).isSome

/--
warning: declaration uses `sorry`
---
warning: This instance has 4 arguments that cannot be inferred using typeclass synthesis. Specifically

  argument 2: `{β : Type}`
  argument 3: `(b : Array β)`
  argument 4: `(a : Array α)`
  argument 6: `⦃h : b = b⦄`

These arguments are not instance-implicit and appear neither in another instance-implicit argument nor the return type, so they cannot be inferred using typeclass synthesis.

Note: This linter can be disabled with `set_option linter.impossibleInstance false`
-/
#guard_msgs in
local instance impossibleWithChain {α β : Type} (b : Array β) (a : Array α) [Inhabited α]
    ⦃h : b = b⦄
    -- Note: `usedA` is a dependency of a dependency of a dependency of the return type
    (usedA : Array α) (i : Fin usedA.size) (j : Fin i.val) :
    Nonempty { a : Array α // a.size = j.val } := sorry

-- The following tests that the impossibleInstance syntax and environment linter
-- only fire on instances. So the following theorem should not be linted by them.
/--
warning: unused variable `β`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
-/
#guard_msgs in
theorem okayAsThm {α β : Type} [Inhabited α] : Nonempty α := ⟨default⟩

run_meta guard (← impossibleInstance.test ``okayAsThm).isNone

end A

namespace B

/--
warning: The declaration `bad` should not be an instance as it is not class-valued.

Note: This linter can be disabled with `set_option linter.nonClassInstance false`
-/
#guard_msgs in
instance bad : Nat := 1

run_meta guard (← nonClassInstance.test ``bad).isSome
instance good : Inhabited Nat := ⟨1⟩

run_meta guard (← nonClassInstance.test ``good).isNone
end B

section setOptionIn

/--
warning: unused variable `β`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
-/
#guard_msgs in
set_option linter.impossibleInstance false in
local instance impossible' {α β : Type} [Inhabited α] : Nonempty α := ⟨default⟩

/--
warning: unused variable `β`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
---
warning: This instance has 1 argument that cannot be inferred using typeclass synthesis. Specifically

  argument 2: `{β : Type}`

These arguments are not instance-implicit and appear neither in another instance-implicit argument nor the return type, so they cannot be inferred using typeclass synthesis.

Note: This linter can be disabled with `set_option linter.impossibleInstance false`
-/
#guard_msgs in
set_option linter.impossibleInstance true in
local instance impossibleControl {α β : Type} [Inhabited α] : Nonempty α := ⟨default⟩

#guard_msgs in
set_option linter.nonClassInstance false in
instance bad' : Nat := 1

/--
@ +3:9...19
warning: The declaration `badControl` should not be an instance as it is not class-valued.

Note: This linter can be disabled with `set_option linter.nonClassInstance false`
-/
#guard_msgs (positions := true) in
set_option linter.nonClassInstance true in
/-- This is a doc string needed for testing the `withDeclRef` function. -/
instance badControl : Nat := 1

end setOptionIn

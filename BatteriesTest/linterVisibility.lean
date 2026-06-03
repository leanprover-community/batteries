module

-- import `Linter` into both private and public scopes for testing
import Batteries.Tactic.Lint.Basic
public import Batteries.Tactic.Lint.Basic

open Batteries.Tactic.Lint

/--
error: Cannot add attribute `[env_linter]`: Declaration `foo` must be marked as `meta`
-/
#guard_msgs (error, drop warning) in
@[env_linter] def foo : Linter := sorry

/--
error: Cannot add attribute `[env_linter]`: Declaration `foo'` must be marked as `meta`
-/
#guard_msgs (error, drop warning) in
@[env_linter] public def foo' : Linter := sorry

/--
error: Cannot add attribute `[env_linter]`: Declaration `_private.BatteriesTest.linterVisibility.0.foo''` must be public
-/
#guard_msgs (error, drop warning) in
@[env_linter] meta def foo'' : Linter := sorry

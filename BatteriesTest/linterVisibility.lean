module

-- import `Linter` into both private and public scopes for testing
import Batteries.Tactic.Lint.Basic
public import Batteries.Tactic.Lint.Basic

open Batteries.Tactic.Lint

/--
error: invalid attribute `env_linter`, declaration `foo` must be marked as `public` and `meta`
-/
#guard_msgs (error, drop warning) in
@[env_linter] def foo : Linter := sorry

/--
error: invalid attribute `env_linter`, declaration `foo'` must be marked as `public` and `meta` but is only marked `public`
-/
#guard_msgs (error, drop warning) in
@[env_linter] public def foo' : Linter := sorry

/--
error: invalid attribute `env_linter`, declaration `foo''` must be marked as `public` and `meta` but is only marked `meta`
-/
#guard_msgs (error, drop warning) in
@[env_linter] meta def foo'' : Linter := sorry

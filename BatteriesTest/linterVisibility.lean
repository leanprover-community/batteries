module

-- import `Linter` into both private and public scopes for testing
import Batteries.Linter.Basic
public import Batteries.Linter.Basic

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

/--
error: Invalid attribute scope: Attribute `[env_linter]` must be global, not `local`
-/
#guard_msgs (error, drop warning) in
@[local env_linter] public meta def foo''' : Linter := sorry

namespace Foo

/--
error: Invalid attribute scope: Attribute `[env_linter]` must be global, not `scoped`
-/
#guard_msgs (error, drop warning) in
@[scoped env_linter] public meta def foo'''' : Linter := sorry

end Foo

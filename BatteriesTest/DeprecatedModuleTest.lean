import BatteriesTest.DeprecatedModule

/--
warning: We can also give more details about the deprecation
'BatteriesTest.DeprecatedModule' has been deprecated: please replace this import by

import Batteries.Tactic.Alias
import Batteries.Tactic.Basic


Note: This linter can be disabled with `set_option linter.deprecated.module false`
---
warning:
'BatteriesTest.DeprecatedModule' has been deprecated: please replace this import by

import Batteries.Tactic.Alias
import Batteries.Tactic.Basic


Note: This linter can be disabled with `set_option linter.deprecated.module false`
-/
#guard_msgs in
/-!
This file imports a deprecated module.
-/

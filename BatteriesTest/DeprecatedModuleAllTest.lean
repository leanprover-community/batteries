module

import all BatteriesTest.DeprecatedModuleNew

/--
warning: Testing public import deprecation
'BatteriesTest.DeprecatedModuleNew' has been deprecated: please replace this import by

import Batteries.Tactic.Alias
import Batteries.Tactic.Basic


Note: This linter can be disabled with `set_option linter.deprecated.module false`
-/
#guard_msgs in
/-!
This file imports a deprecated module with `import all`.
-/

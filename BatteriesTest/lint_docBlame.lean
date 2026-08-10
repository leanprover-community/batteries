module

import Batteries.Tactic.Lint

set_option linter.missingDocs false

public section

-- A docstring is needed here
structure AtLeastThirtySeven where
  -- and here
  val : Nat := 1
  -- but not here
  prop : 37 ≤ val

-- or here (due to being a theorem)
theorem AtLeastThirtySeven.lt (x : AtLeastThirtySeven) : 36 < x.val := x.prop

def foo_bad := 3 -- Needs a docstring
private def foo_ok := 7 -- Doesn't (due to being private)

/--
error: /- The `docBlame` linter reports:
DEFINITIONS ARE MISSING DOCUMENTATION STRINGS:
This linter can be disabled with `@[nolint docBlame]`. -/
#check AtLeastThirtySeven /- inductive missing documentation string -/
#check AtLeastThirtySeven.val /- definition missing documentation string -/
#check foo_bad /- definition missing documentation string -/
-/
#guard_msgs in
#lint- only docBlame

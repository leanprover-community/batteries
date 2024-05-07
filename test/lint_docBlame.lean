import Batteries.Tactic.Lint

set_option linter.missingDocs false

/-- A docstring is needed here -/
structure AtLeastThirtySeven where
  /-- and here -/
  val : Nat := 1
  -- but not here
  prop : 37 ≤ val

-- or here
theorem AtLeastThirtySeven.lt (x : AtLeastThirtySeven) : 36 < x.val := x.prop

#lint- only docBlame

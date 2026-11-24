module

import all BatteriesTest.Internal.PrivateEqnLemmasDownstream

/-! Sees the body of `hiddenQuad` through a chain of `import all`s, for
`BatteriesTest/lint_privateEqnLemmas.lean`. -/

/-- Generates `hiddenQuad.eq_1` in this module. -/
private theorem hiddenQuad_eq (n : Nat) : hiddenQuad n = n + n + n + n := by
  rw [hiddenQuad.eq_1]

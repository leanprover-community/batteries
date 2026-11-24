module

import BatteriesTest.Internal.PrivateEqnLemmasDefs

/-! Imports the definitions without `import all`, for `BatteriesTest/lint_privateEqnLemmas.lean`.
The body of `hiddenDouble` is not visible here, so the names of its equation lemmas are not
reserved, and a hand-written theorem can take one. -/

/-- A hand-written private theorem with the name of an equation lemma of `hiddenDouble`. -/
private theorem hiddenDouble.eq_7 : hiddenDouble 0 = hiddenDouble 0 := rfl

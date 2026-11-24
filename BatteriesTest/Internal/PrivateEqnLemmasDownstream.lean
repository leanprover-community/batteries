module

import all BatteriesTest.Internal.PrivateEqnLemmasDefs

/-! Generates equation lemmas downstream of the definition, for
`BatteriesTest/lint_privateEqnLemmas.lean`. -/

/-- Generates `hiddenTriple.eq_1` in this module. -/
private theorem hiddenTriple_eq (n : Nat) : hiddenTriple n = n + n + n := by
  rw [hiddenTriple.eq_1]

/-- Generates `secretTriple.eq_1` in this module. These names are not reserved here. -/
private theorem secretTriple_eq (n : Nat) : secretTriple n = n + n + n := by
  simp only [secretTriple]

/-- A hand-written private theorem with the name of an equation lemma of `secretTriple`. -/
private theorem secretTriple.eq_7 : secretTriple 0 = 0 := rfl

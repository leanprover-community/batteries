module

/-! Definitions for `BatteriesTest/lint_privateEqnLemmas.lean`. -/

public section

/-- A definition whose body is not exposed, so its equation lemmas are private. -/
def hiddenDouble (n : Nat) : Nat := n + n

/-- A definition whose body is exposed, so its equation lemmas are public. -/
@[expose] def shownDouble (n : Nat) : Nat := n + n

/-- Generates `hiddenDouble.eq_def` and `shownDouble.eq_1`. -/
theorem hiddenDouble_eq_shownDouble (n : Nat) : hiddenDouble n = shownDouble n := by
  rw [hiddenDouble.eq_def, shownDouble.eq_1]

/-- Generates `hiddenDouble.eq_1`. -/
theorem hiddenDouble_eq (n : Nat) : hiddenDouble n = n + n := by rw [hiddenDouble.eq_1]

/-- Generates `hiddenDouble.eq_unfold`. -/
theorem hiddenDouble_eq_fun : hiddenDouble = fun n => n + n := by rw [hiddenDouble.eq_unfold]

/-- A definition whose equation lemmas are first generated downstream. -/
def hiddenTriple (n : Nat) : Nat := n + n + n

/-- A hand-written private theorem, which must still count as hand-written. -/
private theorem hiddenDouble_zero : hiddenDouble 0 = 0 := rfl

/-- A hand-written private theorem with the name of an equation lemma of a later definition. -/
private theorem hiddenLater.eq_1 : True := trivial

/-- A definition declared after a theorem with the name of one of its equation lemmas. -/
def hiddenLater : Nat := 0

/-- A private definition whose equation lemmas are first generated downstream. -/
private def secretTriple (n : Nat) : Nat := n + n + n

/-- A definition whose equation lemmas are first generated through a chain of `import all`s. -/
def hiddenQuad (n : Nat) : Nat := n + n + n + n

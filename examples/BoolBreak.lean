@[simp] theorem false_eq_true : (false = true) = false := sorry

@[simp] theorem true_eq_false : (true = false) = false := sorry

@[simp low] theorem false_eq (b : Bool) : (false = b) = (b = false) := sorry

@[simp low] theorem true_eq (b : Bool) : (true = b) = (b = true) := sorry

example : (true = false) = false := by
  simp

import Std

theorem ofBool_eq_iff_eq (b b' : Bool) : BitVec.ofBool b = BitVec.ofBool b' ↔ b = b' := by
  cases b <;> cases b'
--#print ite_t
example (p q : Prop) (h : ¬p) : p → q ↔ true := by
  std_apply?

--  by_cases h : p <;> simp [h]

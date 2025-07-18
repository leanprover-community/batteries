import Batteries.Data.Stream.Finite

/- Example of a stream type which is not well-founded but has many derivable finite instances. -/
structure Test where
  decr : Bool
  val : Nat
  deriving Repr

instance : Stream Test Nat where
  next? s :=
    if ¬ s.decr then
      some (s.val, {s with val := s.val+1})
    else if s.val ≠ 0 then
      some (s.val-1, {s with val := s.val-1})
    else
      none

instance : Stream.WithNextRelation Test Nat where
  rel s t := t.decr → s.decr ∧ s.val < t.val
  rel_of_next?_eq_some := by
    intro _ _ _ h
    simp [Stream.next?] at h
    split at h
    · cases h
      simp [*]
    · split at h
      · contradiction
      · next h0 =>
        intro h'
        cases h
        constructor
        · exact h'
        · exact Nat.sub_one_lt h0

instance : Stream.Finite (Test.mk true n) :=
  have wf : WellFounded (Stream.RestrictedNext (Test.decr ·)) :=
    Subrelation.wf (fun h => (h.2 h.1).2) (measure Test.val).wf
  Stream.Finite.ofRestrictedNext (p := (Test.decr ·))
    (fun h h' => (h h').1) rfl (wf.apply _)

#guard Stream.Finite.toList (Test.mk true 3) == [2, 1, 0]

/--
error: failed to synthesize
  Stream.Finite { decr := false, val := 3 }

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/
#guard_msgs in
#eval Stream.Finite.toList (Test.mk false 3)

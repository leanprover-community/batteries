import Batteries.Util.ProofWanted

/-!
No unused variable warnings.
-/
#guard_msgs in proof_wanted foo (x : Nat) : True

/-!
When not a proposition, rely on `theorem` command failing.
-/
/--
error: type of theorem 'foo' is not a proposition
  Nat → Nat
-/
#guard_msgs in proof_wanted foo (x : Nat) : Nat

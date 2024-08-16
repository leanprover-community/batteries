import Batteries.Data.Rat.Lemmas

/-!
# Tests for norm_cast involving `Rat`.
-/

set_option linter.missingDocs false

-- set_option trace.Meta.Tactic.simp true

variable (aq bq cq dq : Rat)

example : az = bz ↔ (az : Rat) = bz := by norm_cast

-- zero and one cause special problems
example : aq < (1 : Nat) ↔ (aq : Rat) < (1 : Int) := by norm_cast

--testing numerals
example : ((42 : Nat) : Rat) = 42 := by norm_cast
example : ((42 : Int) : Rat) = 42 := by norm_cast

-- We don't yet have `{n m : Int} : (↑n : Rat) ≤ ↑m ↔ n ≤ m` in Batteries
-- example (n : Int) (h : n + 1 > 0) : ((n + 1 : Int) : Rat) > 0 := by exact_mod_cast h

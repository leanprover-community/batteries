import Std.Tactic.NormCast
import Std.Data.Rat.Lemmas

/-!
# Tests for norm_cast
-/


set_option linter.missingDocs false

-- set_option trace.Meta.Tactic.simp true

variable (an bn cn dn : Nat) (az bz cz dz : Int)
variable (aq bq cq dq : Rat)

example : (an : Int) = bn → an = bn := by intro h; exact_mod_cast h
example : an = bn → (an : Int) = bn := by intro h; exact_mod_cast h
example : az = bz ↔ (az : Rat) = bz := by norm_cast

example : (an : Int) < bn ↔ an < bn := by norm_cast
example : (an : Int) ≠ (bn : Int) ↔ an ≠ bn := by norm_cast

-- zero and one cause special problems
example : az > (1 : Nat) ↔ az > 1 := by norm_cast
example : az > (0 : Nat) ↔ az > 0 := by norm_cast
example : (an : Int) ≠ 0 ↔ an ≠ 0 := by norm_cast
example : aq < (1 : Nat) ↔ (aq : Rat) < (1 : Int) := by norm_cast

example (a b : Nat) (h : False) : (a : Int) < ((2 * b : Nat) : Int) := by
  push_cast
  guard_target = (a : Int) < 2 * (b : Int)
  cases h

example : (an : Int) + bn = (an + bn : Nat) := by norm_cast

example (h : ((an + bn : Nat) : Int) = (an : Int) + (bn : Int)) : True := by
  push_cast at h
  guard_hyp h : (an : Int) + (bn : Int) = (an : Int) + (bn : Int)
  trivial

example (h : ((an * bn : Nat) : Int) = (an : Int) * (bn : Int)) : True := by
  push_cast at h
  guard_hyp h : (an : Int) * (bn : Int) = (an : Int) * (bn : Int)
  trivial

--testing numerals
example : ((42 : Nat) : Int) = 42 := by norm_cast
example : ((42 : Nat) : Rat) = 42 := by norm_cast
example : ((42 : Int) : Rat) = 42 := by norm_cast

structure p (n : Int)
example : p 42 := by
  norm_cast
  guard_target = p 42
  exact ⟨⟩

-- We don't yet have `{n m : Int} : (↑n : Rat) ≤ ↑m ↔ n ≤ m` in Std
-- example (n : Int) (h : n + 1 > 0) : ((n + 1 : Int) : Rat) > 0 := by exact_mod_cast h

example : an + bn = 1 ↔ (an + bn : Int) = 1 := by norm_cast

example (h : bn ≤ an) : an - bn = 1 ↔ (an - bn : Int) = 1 := by norm_cast

example (k : Nat) {x y : Nat} (h : ((x + y + k : Nat) : Int) = 0) : x + y + k = 0 := by
  push_cast at h
  guard_hyp h : (x : Int) + y + k = 0
  assumption_mod_cast

example (a b : Nat) (h2 : ((a + b + 0 : Nat) : Int) = 10) :
    ((a + b : Nat) : Int) = 10 := by
  push_cast
  push_cast [Int.add_zero] at h2
  exact h2

theorem b (h g : true) : true ∧ true := by
  constructor
  assumption_mod_cast
  assumption_mod_cast

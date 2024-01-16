import Std.Data.Int.DivMod
import Std.Data.Nat.Gcd
import Std.Tactic.PermuteGoals
import Std.Tactic.Replace

namespace Int

/-!
## Int.gcd
-/

theorem gcd_dvd_left {a b : Int} : (gcd a b : Int) ∣ a := sorry
theorem gcd_dvd_right {a b : Int} : (gcd a b : Int) ∣ b := sorry

/-!
## Small solutions to divisibility constraints.
-/

/--
Given a solution `x` to a divisibility constraint `a ∣ b * x + c`,
then `x % d` is another solution as long as `(a / gcd a b) | d`.
-/
theorem dvd_mul_emod_add_of_dvd_mul_add {a b c d x : Int}
    (w : a ∣ b * x + c) (h : (a / gcd a b) ∣ d) :
    a ∣ b * (x % d) + c := by
  obtain ⟨p, w⟩ := w
  obtain ⟨q, rfl⟩ := h
  rw [Int.emod_def, Int.mul_sub, Int.sub_eq_add_neg, Int.add_right_comm, w,
    Int.dvd_add_right (Int.dvd_mul_right _ _), ← Int.mul_assoc, ← Int.mul_assoc, Int.dvd_neg,
    ← Int.mul_ediv_assoc b gcd_dvd_left, Int.mul_comm b a, Int.mul_ediv_assoc a gcd_dvd_right,
    Int.mul_assoc, Int.mul_assoc]
  apply Int.dvd_mul_right

theorem dvd_emod_add_of_dvd_add {a c d x : Int} (w : a ∣ x + c) : a ∣ (x % d) + c := by
  rw [← Int.one_mul x] at w
  rw [← Int.one_mul (x % d)]
  apply dvd_mul_emod_add_of_dvd_mul_add w
  sorry

/-! ## lcm -/

/-- Computes the least common multiple of two integers, as a `Nat`. -/
def lcm (m n : Int) : Nat := m.natAbs.lcm n.natAbs

theorem lcm_pos (hm : 0 < m) (hn : 0 < n) : 0 < lcm m n := sorry

theorem dvd_lcm_right {a b : Int} : b ∣ lcm a b := sorry

theorem exists_add_of_le {a b : Int} (h : a ≤ b) : ∃ c : Nat, b = a + c := sorry

instance : Trans (fun x y : Int => x ≤ y) (fun x y : Int => x ≤ y) (fun x y : Int => x ≤ y) := ⟨Int.le_trans⟩

theorem ediv_pos_of_dvd {a b : Int} (ha : 0 < a) (hb : 0 ≤ b) (w : b ∣ a) : 0 < a / b := sorry

/--
Given lower and upper bounds `p ≤ a * x` and `b * x ≤ q` (here `0 < a` and `0 < b`)
for an integer `x` and a divisibility constraint `d ∣ c * x + s` (with `0 < d`),
we can find a `k`, with explicit bounds `0 ≤ k < lcm a (a * d / gcd (a * d) c)`
satisfying
-/
theorem cooper_resolution_dvd_left
    {a b c d s p q : Int} (a_pos : 0 < a) (b_pos : 0 < b) (d_pos : 0 < d)
    (lower : p ≤ a * x) (upper : b * x ≤ q) (dvd : d ∣ c * x + s) :
    ∃ k, 0 ≤ k ∧ k < lcm a (a * d / gcd (a * d) c) ∧
      b * p + b * k ≤ a * q ∧
      a ∣ k + p ∧
      a * d ∣ c * k + c * p + a * s := by
  obtain ⟨k', w⟩ := exists_add_of_le lower
  refine ⟨k' % ?_, Nat.zero_le _, ?_, ?_, ?_, ?_⟩
  on_goal 2 =>
    exact Nat.mod_lt _ (lcm_pos a_pos (Int.ediv_pos_of_dvd (Int.mul_pos a_pos d_pos)
      (Int.ofNat_nonneg _) gcd_dvd_left))
  · replace upper : a * b * x ≤ a * q :=
      Int.mul_assoc _ _ _ ▸ Int.mul_le_mul_of_nonneg_left upper (Int.le_of_lt a_pos)
    rw [Int.mul_right_comm, w, Int.add_mul, Int.mul_comm p b, Int.mul_comm _ b] at upper
    calc
      _ ≤ _ := Int.add_le_add_left
        (Int.mul_le_mul_of_nonneg_left (Int.ofNat_le.mpr <| Nat.mod_le _ _) (Int.le_of_lt b_pos)) _
      _ ≤ _ := upper
  · exact Int.ofNat_emod _ _ ▸ dvd_emod_add_of_dvd_add ⟨x, by rw [w, Int.add_comm]⟩
  · rw [Int.add_assoc, Int.ofNat_emod]
    apply dvd_mul_emod_add_of_dvd_mul_add
    · obtain ⟨z, r⟩ := dvd
      refine ⟨z, ?_⟩
      rw [Int.mul_assoc, ← r, Int.mul_add, Int.mul_comm c x, ← Int.mul_assoc, w, Int.add_mul,
        Int.mul_comm c, Int.mul_comm c, ← Int.add_assoc, Int.add_comm (p * c)]
    · exact Int.dvd_lcm_right

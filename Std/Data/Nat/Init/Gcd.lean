import Std.Data.Nat.Init.Basic
import Std.Data.Nat.Init.Dvd

namespace Nat

theorem gcd_rec (m n : Nat) : gcd m n = gcd (n % m) m :=
  match m with
  | 0 => by have := (mod_zero n).symm; rwa [gcd_zero_right]
  | _ + 1 => by simp [gcd_succ]

@[elab_as_elim] theorem gcd.induction {P : Nat → Nat → Prop} (m n : Nat)
    (H0 : ∀n, P 0 n) (H1 : ∀ m n, 0 < m → P (n % m) m → P m n) : P m n :=
  Nat.strongInductionOn (motive := fun m => ∀ n, P m n) m
    (fun
    | 0, _ => H0
    | _+1, IH => fun _ => H1 _ _ (succ_pos _) (IH _ (mod_lt _ (succ_pos _)) _) )
    n

theorem gcd_dvd (m n : Nat) : (gcd m n ∣ m) ∧ (gcd m n ∣ n) := by
  induction m, n using gcd.induction with
  | H0 n => rw [gcd_zero_left]; exact ⟨Nat.dvd_zero n, Nat.dvd_refl n⟩
  | H1 m n _ IH => rw [← gcd_rec] at IH; exact ⟨IH.2, (dvd_mod_iff IH.2).1 IH.1⟩

theorem gcd_dvd_left (m n : Nat) : gcd m n ∣ m := (gcd_dvd m n).left

theorem gcd_dvd_right (m n : Nat) : gcd m n ∣ n := (gcd_dvd m n).right

theorem gcd_le_left (n) (h : 0 < m) : gcd m n ≤ m := le_of_dvd h <| gcd_dvd_left m n

theorem gcd_le_right (n) (h : 0 < n) : gcd m n ≤ n := le_of_dvd h <| gcd_dvd_right m n

theorem dvd_gcd : k ∣ m → k ∣ n → k ∣ gcd m n := by
  induction m, n using gcd.induction with intro km kn
  | H0 n => rw [gcd_zero_left]; exact kn
  | H1 n m _ IH => rw [gcd_rec]; exact IH ((dvd_mod_iff km).2 kn) km

end Nat

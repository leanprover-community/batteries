/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro
-/
import Std.Data.Nat.Lemmas

/-!
# Definitions and properties of `gcd`, `lcm`, and `coprime`

-/

namespace Nat

theorem gcd_rec (m n : Nat) : gcd m n = gcd (n % m) m :=
  match m with
  | 0 => by have := (mod_zero n).symm; rwa [gcd_zero_right]
  | _ + 1 => by simp [gcd_succ]

@[elabAsElim] theorem gcd.induction {P : Nat → Nat → Prop} (m n : Nat)
    (H0 : ∀n, P 0 n) (H1 : ∀ m n, 0 < m → P (n % m) m → P m n) : P m n :=
  Nat.strongInductionOn (motive := fun m => ∀ n, P m n) m
    (fun
    | 0, _ => H0
    | _+1, IH => fun _ => H1 _ _ (succ_pos _) (IH _ (mod_lt _ (succ_pos _)) _) )
    n

/-- The least common multiple of `m` and `n`, defined using `gcd`. -/
def lcm (m n : Nat) : Nat := m * n / gcd m n

/-- `m` and `n` are coprime, or relatively prime, if their `gcd` is 1. -/
@[reducible] def coprime (m n : Nat) : Prop := gcd m n = 1

---

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

theorem dvd_gcd_iff : k ∣ gcd m n ↔ k ∣ m ∧ k ∣ n :=
  ⟨fun h => let ⟨h₁, h₂⟩ := gcd_dvd m n; ⟨Nat.dvd_trans h h₁, Nat.dvd_trans h h₂⟩,
   fun ⟨h₁, h₂⟩ => dvd_gcd h₁ h₂⟩

theorem gcd_comm (m n : Nat) : gcd m n = gcd n m :=
  dvd_antisymm
    (dvd_gcd (gcd_dvd_right m n) (gcd_dvd_left m n))
    (dvd_gcd (gcd_dvd_right n m) (gcd_dvd_left n m))

theorem gcd_eq_left_iff_dvd : m ∣ n ↔ gcd m n = m :=
  ⟨fun h => by rw [gcd_rec, mod_eq_zero_of_dvd h, gcd_zero_left],
   fun h => h ▸ gcd_dvd_right m n⟩

theorem gcd_eq_right_iff_dvd : m ∣ n ↔ gcd n m = m := by
  rw [gcd_comm]; exact gcd_eq_left_iff_dvd

theorem gcd_assoc (m n k : Nat) : gcd (gcd m n) k = gcd m (gcd n k) :=
  dvd_antisymm
    (dvd_gcd
      (Nat.dvd_trans (gcd_dvd_left (gcd m n) k) (gcd_dvd_left m n))
      (dvd_gcd (Nat.dvd_trans (gcd_dvd_left (gcd m n) k) (gcd_dvd_right m n))
        (gcd_dvd_right (gcd m n) k)))
    (dvd_gcd
      (dvd_gcd (gcd_dvd_left m (gcd n k))
        (Nat.dvd_trans (gcd_dvd_right m (gcd n k)) (gcd_dvd_left n k)))
      (Nat.dvd_trans (gcd_dvd_right m (gcd n k)) (gcd_dvd_right n k)))

@[simp] theorem gcd_one_right (n : Nat) : gcd n 1 = 1 := (gcd_comm n 1).trans (gcd_one_left n)

theorem gcd_mul_left (m n k : Nat) : gcd (m * n) (m * k) = m * gcd n k := by
  induction n, k using gcd.induction with
  | H0 k => simp
  | H1 n k _ IH => rwa [←mul_mod_mul_left, ←gcd_rec, ←gcd_rec] at IH

theorem gcd_mul_right (m n k : Nat) : gcd (m * n) (k * n) = gcd m k * n := by
  rw [Nat.mul_comm m n, Nat.mul_comm k n, Nat.mul_comm (gcd m k) n, gcd_mul_left]

theorem gcd_pos_of_pos_left {m : Nat} (n : Nat) (mpos : 0 < m) : 0 < gcd m n :=
  pos_of_dvd_of_pos (gcd_dvd_left m n) mpos

theorem gcd_pos_of_pos_right (m : Nat) {n : Nat} (npos : 0 < n) : 0 < gcd m n :=
  pos_of_dvd_of_pos (gcd_dvd_right m n) npos

theorem div_gcd_pos_of_pos_left (b : Nat) (h : 0 < a) : 0 < a / a.gcd b :=
  (Nat.le_div_iff_mul_le <| Nat.gcd_pos_of_pos_left _ h).2 (Nat.one_mul _ ▸ Nat.gcd_le_left _ h)

theorem div_gcd_pos_of_pos_right (a : Nat) (h : 0 < b) : 0 < b / a.gcd b :=
  (Nat.le_div_iff_mul_le <| Nat.gcd_pos_of_pos_right _ h).2 (Nat.one_mul _ ▸ Nat.gcd_le_right _ h)

theorem eq_zero_of_gcd_eq_zero_left {m n : Nat} (H : gcd m n = 0) : m = 0 :=
  match eq_zero_or_pos m with
  | .inl H0 => H0
  | .inr H1 => absurd (Eq.symm H) (ne_of_lt (gcd_pos_of_pos_left _ H1))

theorem eq_zero_of_gcd_eq_zero_right {m n : Nat} (H : gcd m n = 0) : n = 0 := by
  rw [gcd_comm] at H
  exact eq_zero_of_gcd_eq_zero_left H

theorem gcd_div {m n k : Nat} (H1 : k ∣ m) (H2 : k ∣ n) :
    gcd (m / k) (n / k) = gcd m n / k :=
  match eq_zero_or_pos k with
  | .inl H0 => by simp [H0]
  | .inr H3 => by
    apply Nat.eq_of_mul_eq_mul_right H3
    rw [Nat.div_mul_cancel (dvd_gcd H1 H2), ← gcd_mul_right,
        Nat.div_mul_cancel H1, Nat.div_mul_cancel H2]

theorem gcd_dvd_gcd_of_dvd_left {m k : Nat} (n : Nat) (H : m ∣ k) : gcd m n ∣ gcd k n :=
  dvd_gcd (Nat.dvd_trans (gcd_dvd_left m n) H) (gcd_dvd_right m n)

theorem gcd_dvd_gcd_of_dvd_right {m k : Nat} (n : Nat) (H : m ∣ k) : gcd n m ∣ gcd n k :=
  dvd_gcd (gcd_dvd_left n m) (Nat.dvd_trans (gcd_dvd_right n m) H)

theorem gcd_dvd_gcd_mul_left (m n k : Nat) : gcd m n ∣ gcd (k * m) n :=
  gcd_dvd_gcd_of_dvd_left _ (Nat.dvd_mul_left _ _)

theorem gcd_dvd_gcd_mul_right (m n k : Nat) : gcd m n ∣ gcd (m * k) n :=
  gcd_dvd_gcd_of_dvd_left _ (Nat.dvd_mul_right _ _)

theorem gcd_dvd_gcd_mul_left_right (m n k : Nat) : gcd m n ∣ gcd m (k * n) :=
  gcd_dvd_gcd_of_dvd_right _ (Nat.dvd_mul_left _ _)

theorem gcd_dvd_gcd_mul_right_right (m n k : Nat) : gcd m n ∣ gcd m (n * k) :=
  gcd_dvd_gcd_of_dvd_right _ (Nat.dvd_mul_right _ _)

theorem gcd_eq_left {m n : Nat} (H : m ∣ n) : gcd m n = m :=
  dvd_antisymm (gcd_dvd_left _ _) (dvd_gcd (Nat.dvd_refl _) H)

theorem gcd_eq_right {m n : Nat} (H : n ∣ m) : gcd m n = n := by
  rw [gcd_comm, gcd_eq_left H]

@[simp] theorem gcd_mul_left_left (m n : Nat) : gcd (m * n) n = n :=
  dvd_antisymm (gcd_dvd_right _ _) (dvd_gcd (Nat.dvd_mul_left _ _) (Nat.dvd_refl _))

@[simp] theorem gcd_mul_left_right (m n : Nat) : gcd n (m * n) = n := by
  rw [gcd_comm, gcd_mul_left_left]

@[simp] theorem gcd_mul_right_left (m n : Nat) : gcd (n * m) n = n := by
  rw [Nat.mul_comm, gcd_mul_left_left]

@[simp] theorem gcd_mul_right_right (m n : Nat) : gcd n (n * m) = n := by
  rw [gcd_comm, gcd_mul_right_left]

@[simp] theorem gcd_gcd_self_right_left (m n : Nat) : gcd m (gcd m n) = gcd m n :=
  dvd_antisymm (gcd_dvd_right _ _) (dvd_gcd (gcd_dvd_left _ _) (Nat.dvd_refl _))

@[simp] theorem gcd_gcd_self_right_right (m n : Nat) : gcd m (gcd n m) = gcd n m := by
  rw [gcd_comm n m, gcd_gcd_self_right_left]

@[simp] theorem gcd_gcd_self_left_right (m n : Nat) : gcd (gcd n m) m = gcd n m := by
  rw [gcd_comm, gcd_gcd_self_right_right]

@[simp] theorem gcd_gcd_self_left_left (m n : Nat) : gcd (gcd m n) m = gcd m n := by
  rw [gcd_comm m n, gcd_gcd_self_left_right]

theorem gcd_add_mul_self (m n k : Nat) : gcd m (n + k * m) = gcd m n := by
  simp [gcd_rec m (n + k * m), gcd_rec m n]

theorem gcd_eq_zero_iff {i j : Nat} : gcd i j = 0 ↔ i = 0 ∧ j = 0 :=
  ⟨fun h => ⟨eq_zero_of_gcd_eq_zero_left h, eq_zero_of_gcd_eq_zero_right h⟩,
   fun h => by simp [h]⟩

/-! ### `lcm` -/

theorem lcm_comm (m n : Nat) : lcm m n = lcm n m := by
  rw [lcm, lcm, Nat.mul_comm n m, gcd_comm n m]

@[simp] theorem lcm_zero_left (m : Nat) : lcm 0 m = 0 := by simp [lcm]

@[simp] theorem lcm_zero_right (m : Nat) : lcm m 0 = 0 := by simp [lcm]

@[simp] theorem lcm_one_left (m : Nat) : lcm 1 m = m := by simp [lcm]

@[simp] theorem lcm_one_right (m : Nat) : lcm m 1 = m := by simp [lcm]

@[simp] theorem lcm_self (m : Nat) : lcm m m = m := by
  match eq_zero_or_pos m with
  | .inl h => rw [h, lcm_zero_left]
  | .inr h => simp [lcm, Nat.mul_div_cancel _ h]

theorem dvd_lcm_left (m n : Nat) : m ∣ lcm m n :=
  ⟨n / gcd m n, by rw [← Nat.mul_div_assoc m (Nat.gcd_dvd_right m n)]; rfl⟩

theorem dvd_lcm_right (m n : Nat) : n ∣ lcm m n := lcm_comm n m ▸ dvd_lcm_left n m

theorem gcd_mul_lcm (m n : Nat) : gcd m n * lcm m n = m * n := by
  rw [lcm, Nat.mul_div_cancel' (Nat.dvd_trans (gcd_dvd_left m n) (Nat.dvd_mul_right m n))]

theorem lcm_dvd {m n k : Nat} (H1 : m ∣ k) (H2 : n ∣ k) : lcm m n ∣ k := by
  match eq_zero_or_pos k with
  | .inl h => rw [h]; exact Nat.dvd_zero _
  | .inr kpos =>
    apply Nat.dvd_of_mul_dvd_mul_left (gcd_pos_of_pos_left n (pos_of_dvd_of_pos H1 kpos))
    rw [gcd_mul_lcm, ← gcd_mul_right, Nat.mul_comm n k]
    exact dvd_gcd (Nat.mul_dvd_mul_left _ H2) (Nat.mul_dvd_mul_right H1 _)

theorem lcm_assoc (m n k : Nat) : lcm (lcm m n) k = lcm m (lcm n k) :=
dvd_antisymm
  (lcm_dvd
    (lcm_dvd (dvd_lcm_left m (lcm n k)) (Nat.dvd_trans (dvd_lcm_left n k) (dvd_lcm_right m (lcm n k))))
    (Nat.dvd_trans (dvd_lcm_right n k) (dvd_lcm_right m (lcm n k))))
  (lcm_dvd
    (Nat.dvd_trans (dvd_lcm_left m n) (dvd_lcm_left (lcm m n) k))
    (lcm_dvd (Nat.dvd_trans (dvd_lcm_right m n) (dvd_lcm_left (lcm m n) k))
      (dvd_lcm_right (lcm m n) k)))

theorem lcm_ne_zero (hm : m ≠ 0) (hn : n ≠ 0) : lcm m n ≠ 0 := by
  intro h
  have h1 := gcd_mul_lcm m n
  rw [h, Nat.mul_zero] at h1
  match mul_eq_zero.1 h1.symm with
  | .inl hm1 => exact hm hm1
  | .inr hn1 => exact hn hn1

/-!
### `coprime`

See also `nat.coprime_of_dvd` and `nat.coprime_of_dvd'` to prove `nat.coprime m n`.
-/

instance (m n : Nat) : Decidable (coprime m n) := inferInstanceAs (Decidable (_ = 1))

theorem coprime_iff_gcd_eq_one : coprime m n ↔ gcd m n = 1 := .rfl

theorem coprime.gcd_eq_one : coprime m n → gcd m n = 1 := id

theorem coprime.symm : coprime n m → coprime m n := (gcd_comm m n).trans

theorem coprime_comm : coprime n m ↔ coprime m n := ⟨coprime.symm, coprime.symm⟩

theorem coprime.dvd_of_dvd_mul_right (H1 : coprime k n) (H2 : k ∣ m * n) : k ∣ m := by
  let t := dvd_gcd (Nat.dvd_mul_left k m) H2
  rwa [gcd_mul_left, H1.gcd_eq_one, Nat.mul_one] at t

theorem coprime.dvd_of_dvd_mul_left (H1 : coprime k m) (H2 : k ∣ m * n) : k ∣ n :=
  H1.dvd_of_dvd_mul_right (by rwa [Nat.mul_comm])

theorem coprime.gcd_mul_left_cancel (m : Nat) (H : coprime k n) : gcd (k * m) n = gcd m n :=
  have H1 : coprime (gcd (k * m) n) k := by
    rw [coprime, Nat.gcd_assoc, H.symm.gcd_eq_one, gcd_one_right]
  dvd_antisymm
    (dvd_gcd (H1.dvd_of_dvd_mul_left (gcd_dvd_left _ _)) (gcd_dvd_right _ _))
    (gcd_dvd_gcd_mul_left _ _ _)

theorem coprime.gcd_mul_right_cancel (m : Nat) (H : coprime k n) : gcd (m * k) n = gcd m n := by
  rw [Nat.mul_comm m k, H.gcd_mul_left_cancel m]

theorem coprime.gcd_mul_left_cancel_right (n : Nat)
    (H : coprime k m) : gcd m (k * n) = gcd m n := by
  rw [gcd_comm m n, gcd_comm m (k * n), H.gcd_mul_left_cancel n]

theorem coprime.gcd_mul_right_cancel_right (n : Nat)
    (H : coprime k m) : gcd m (n * k) = gcd m n := by
  rw [Nat.mul_comm n k, H.gcd_mul_left_cancel_right n]

theorem coprime_div_gcd_div_gcd
    (H : 0 < gcd m n) : coprime (m / gcd m n) (n / gcd m n) := by
  rw [coprime_iff_gcd_eq_one, gcd_div (gcd_dvd_left m n) (gcd_dvd_right m n), Nat.div_self H]

theorem not_coprime_of_dvd_of_dvd (dgt1 : 1 < d) (Hm : d ∣ m) (Hn : d ∣ n) : ¬ coprime m n :=
  fun co => Nat.not_le_of_gt dgt1 <| Nat.le_of_dvd Nat.zero_lt_one <| by
    rw [← co.gcd_eq_one]; exact dvd_gcd Hm Hn

theorem exists_coprime (H : 0 < gcd m n) :
    ∃ m' n', coprime m' n' ∧ m = m' * gcd m n ∧ n = n' * gcd m n :=
  ⟨_, _, coprime_div_gcd_div_gcd H,
    (Nat.div_mul_cancel (gcd_dvd_left m n)).symm,
    (Nat.div_mul_cancel (gcd_dvd_right m n)).symm⟩

theorem exists_coprime' (H : 0 < gcd m n) :
    ∃ g m' n', 0 < g ∧ coprime m' n' ∧ m = m' * g ∧ n = n' * g :=
  let ⟨m', n', h⟩ := exists_coprime H; ⟨_, m', n', H, h⟩

theorem coprime.mul (H1 : coprime m k) (H2 : coprime n k) : coprime (m * n) k :=
  (H1.gcd_mul_left_cancel n).trans H2

theorem coprime.mul_right (H1 : coprime k m) (H2 : coprime k n) : coprime k (m * n) :=
  (H1.symm.mul H2.symm).symm

theorem coprime.coprime_dvd_left (H1 : m ∣ k) (H2 : coprime k n) : coprime m n := by
  apply eq_one_of_dvd_one
  rw [coprime] at H2
  have := Nat.gcd_dvd_gcd_of_dvd_left n H1
  rwa [← H2]

theorem coprime.coprime_dvd_right (H1 : n ∣ m) (H2 : coprime k m) : coprime k n :=
  (H2.symm.coprime_dvd_left H1).symm

theorem coprime.coprime_mul_left (H : coprime (k * m) n) : coprime m n :=
  H.coprime_dvd_left (Nat.dvd_mul_left _ _)

theorem coprime.coprime_mul_right (H : coprime (m * k) n) : coprime m n :=
  H.coprime_dvd_left (Nat.dvd_mul_right _ _)

theorem coprime.coprime_mul_left_right (H : coprime m (k * n)) : coprime m n :=
  H.coprime_dvd_right (Nat.dvd_mul_left _ _)

theorem coprime.coprime_mul_right_right (H : coprime m (n * k)) : coprime m n :=
  H.coprime_dvd_right (Nat.dvd_mul_right _ _)

theorem coprime.coprime_div_left (cmn : coprime m n) (dvd : a ∣ m) : coprime (m / a) n := by
  match eq_zero_or_pos a with
  | .inl h0 =>
    rw [h0] at dvd
    rw [Nat.eq_zero_of_zero_dvd dvd] at cmn ⊢
    simp; assumption
  | .inr hpos =>
    let ⟨k, hk⟩ := dvd
    rw [hk, Nat.mul_div_cancel_left _ hpos]
    rw [hk] at cmn
    exact cmn.coprime_mul_left

theorem coprime.coprime_div_right (cmn : coprime m n) (dvd : a ∣ n) : coprime m (n / a) :=
  (cmn.symm.coprime_div_left dvd).symm

theorem coprime_mul_iff_left : coprime (m * n) k ↔ coprime m k ∧ coprime n k :=
  ⟨fun h => ⟨h.coprime_mul_right, h.coprime_mul_left⟩,
   fun ⟨h, _⟩ => by rwa [coprime_iff_gcd_eq_one, h.gcd_mul_left_cancel n]⟩

theorem coprime_mul_iff_right : coprime k (m * n) ↔ coprime k m ∧ coprime k n := by
  rw [@coprime_comm k, @coprime_comm k, @coprime_comm k, coprime_mul_iff_left]

theorem coprime.gcd_left (k : Nat) (hmn : coprime m n) : coprime (gcd k m) n :=
  hmn.coprime_dvd_left <| gcd_dvd_right k m

theorem coprime.gcd_right (k : Nat) (hmn : coprime m n) : coprime m (gcd k n) :=
  hmn.coprime_dvd_right <| gcd_dvd_right k n

theorem coprime.gcd_both (k l : Nat) (hmn : coprime m n) : coprime (gcd k m) (gcd l n) :=
  (hmn.gcd_left k).gcd_right l

theorem coprime.mul_dvd_of_dvd_of_dvd (hmn : coprime m n) (hm : m ∣ a) (hn : n ∣ a) : m * n ∣ a :=
  let ⟨_, hk⟩ := hm
  hk.symm ▸ Nat.mul_dvd_mul_left _ (hmn.symm.dvd_of_dvd_mul_left (hk ▸ hn))

@[simp] theorem coprime_zero_left (n : Nat) : coprime 0 n ↔ n = 1 := by simp [coprime]

@[simp] theorem coprime_zero_right (n : Nat) : coprime n 0 ↔ n = 1 := by simp [coprime]

theorem coprime_one_left : ∀ n, coprime 1 n := gcd_one_left

theorem coprime_one_right : ∀ n, coprime n 1 := gcd_one_right

@[simp] theorem coprime_one_left_eq_true (n) : coprime 1 n = True := eq_true (coprime_one_left _)

@[simp] theorem coprime_one_right_eq_true (n) : coprime n 1 = True := eq_true (coprime_one_right _)

@[simp] theorem coprime_self (n : Nat) : coprime n n ↔ n = 1 := by simp [coprime]

theorem coprime.pow_left (n : Nat) (H1 : coprime m k) : coprime (m ^ n) k := by
  induction n with
  | zero => exact coprime_one_left _
  | succ n ih => have hm := H1.mul ih; rwa [Nat.pow_succ, Nat.mul_comm]

theorem coprime.pow_right (n : Nat) (H1 : coprime k m) : coprime k (m ^ n) :=
  (H1.symm.pow_left n).symm

theorem coprime.pow {k l : Nat} (m n : Nat) (H1 : coprime k l) : coprime (k ^ m) (l ^ n) :=
  (H1.pow_left _).pow_right _

theorem coprime.eq_one_of_dvd {k m : Nat} (H : coprime k m) (d : k ∣ m) : k = 1 := by
  rw [← H.gcd_eq_one, gcd_eq_left d]

/-- Represent a divisor of `m * n` as a product of a divisor of `m` and a divisor of `n`. -/
def prod_dvd_and_dvd_of_dvd_prod {k m n : Nat} (H : k ∣ m * n) :
    {d : {m' // m' ∣ m} × {n' // n' ∣ n} // k = d.1.val * d.2.val} :=
  if h0 : gcd k m = 0 then
    ⟨⟨⟨0, eq_zero_of_gcd_eq_zero_right h0 ▸ Nat.dvd_refl 0⟩,
      ⟨n, Nat.dvd_refl n⟩⟩,
      eq_zero_of_gcd_eq_zero_left h0 ▸ (Nat.zero_mul n).symm⟩
  else by
    have hd : gcd k m * (k / gcd k m) = k := Nat.mul_div_cancel' (gcd_dvd_left k m)
    refine ⟨⟨⟨gcd k m, gcd_dvd_right k m⟩, ⟨k / gcd k m, ?_⟩⟩, hd.symm⟩
    apply Nat.dvd_of_mul_dvd_mul_left (Nat.pos_of_ne_zero h0)
    rw [hd, ← gcd_mul_right]
    exact Nat.dvd_gcd (Nat.dvd_mul_right _ _) H

theorem gcd_mul_dvd_mul_gcd (k m n : Nat) : gcd k (m * n) ∣ gcd k m * gcd k n := by
  let ⟨⟨⟨m', hm'⟩, ⟨n', hn'⟩⟩, (h : gcd k (m * n) = m' * n')⟩ :=
    prod_dvd_and_dvd_of_dvd_prod <| gcd_dvd_right k (m * n)
  rw [h]
  have h' : m' * n' ∣ k := h ▸ gcd_dvd_left ..
  exact Nat.mul_dvd_mul
    (dvd_gcd (Nat.dvd_trans (Nat.dvd_mul_right m' n') h') hm')
    (dvd_gcd (Nat.dvd_trans (Nat.dvd_mul_left n' m') h') hn')

theorem coprime.gcd_mul (k : Nat) (h : coprime m n) : gcd k (m * n) = gcd k m * gcd k n :=
  dvd_antisymm
    (gcd_mul_dvd_mul_gcd k m n)
    ((h.gcd_both k k).mul_dvd_of_dvd_of_dvd
      (gcd_dvd_gcd_mul_right_right ..)
      (gcd_dvd_gcd_mul_left_right ..))

theorem gcd_mul_gcd_of_coprime_of_mul_eq_mul
    (cop : coprime c d) (h : a * b = c * d) : a.gcd c * b.gcd c = c := by
  apply dvd_antisymm
  · apply ((cop.gcd_left _).mul (cop.gcd_left _)).dvd_of_dvd_mul_right
    rw [← h]
    apply Nat.mul_dvd_mul (gcd_dvd ..).1 (gcd_dvd ..).1
  · rw [gcd_comm a, gcd_comm b]
    refine Nat.dvd_trans ?_ (gcd_mul_dvd_mul_gcd ..)
    rw [h, gcd_mul_right_right d c]; apply Nat.dvd_refl

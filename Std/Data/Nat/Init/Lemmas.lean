/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad, Mario Carneiro
-/
import Std.Tactic.Alias

namespace Nat

/-! ### le/lt -/

theorem ne_of_gt {a b : Nat} (h : b < a) : a ≠ b := (ne_of_lt h).symm

protected theorem pos_of_ne_zero {n : Nat} : n ≠ 0 → 0 < n := (eq_zero_or_pos n).resolve_left

@[simp] protected theorem not_le {a b : Nat} : ¬ a ≤ b ↔ b < a :=
  ⟨Nat.gt_of_not_le, Nat.not_le_of_gt⟩

protected alias ⟨lt_of_not_ge, _⟩ := Nat.not_le
protected alias ⟨lt_of_not_le, not_le_of_lt⟩ := Nat.not_le
protected alias ⟨_, lt_le_asymm⟩ := Nat.not_le

@[simp] protected theorem not_lt {a b : Nat} : ¬ a < b ↔ b ≤ a :=
  ⟨Nat.ge_of_not_lt, flip Nat.not_le_of_gt⟩

protected alias ⟨le_of_not_gt, not_lt_of_ge⟩ := Nat.not_lt
protected alias ⟨le_of_not_lt, not_lt_of_le⟩ := Nat.not_lt
protected alias ⟨_, le_lt_asymm⟩ := Nat.not_lt

alias ne_of_lt' := ne_of_gt

protected theorem le_of_not_le {a b : Nat} (h : ¬ b ≤ a) : a ≤ b := Nat.le_of_lt (Nat.not_le.1 h)
protected alias le_of_not_ge := Nat.le_of_not_le

protected theorem le_antisymm_iff {a b : Nat} : a = b ↔ a ≤ b ∧ b ≤ a :=
  ⟨fun | rfl => ⟨Nat.le_refl _, Nat.le_refl _⟩, fun ⟨hle, hge⟩ => Nat.le_antisymm hle hge⟩
protected alias eq_iff_le_and_ge := Nat.le_antisymm_iff

protected theorem lt_or_gt_of_ne {a b : Nat} : a ≠ b → a < b ∨ b < a := by
  rw [← Nat.not_le, ← Nat.not_le, ← Decidable.not_and_iff_or_not_not, and_comm]
  exact mt Nat.le_antisymm_iff.2
protected alias lt_or_lt_of_ne := Nat.lt_or_gt_of_ne
@[deprecated] protected alias lt_connex := Nat.lt_or_gt_of_ne



/-! ## zero/one/two -/

protected theorem pos_iff_ne_zero : 0 < n ↔ n ≠ 0 := ⟨ne_of_gt, Nat.pos_of_ne_zero⟩

/-! ### succ/pred -/

theorem succ_pred_eq_of_pos : ∀ {n}, 0 < n → succ (pred n) = n
  | _+1, _ => rfl

theorem exists_eq_succ_of_ne_zero : ∀ {n}, n ≠ 0 → ∃ k, n = succ k
  | _+1, _ => ⟨_, rfl⟩

/-! ### add -/

protected theorem add_le_add_iff_right {n : Nat} : m + n ≤ k + n ↔ m ≤ k :=
  ⟨Nat.le_of_add_le_add_right, fun h => Nat.add_le_add_right h _⟩

theorem eq_zero_of_add_eq_zero : ∀ {n m}, n + m = 0 → n = 0 ∧ m = 0
  | 0, 0, _ => ⟨rfl, rfl⟩
  | _+1, 0, h => Nat.noConfusion h

protected theorem eq_zero_of_add_eq_zero_left (h : n + m = 0) : m = 0 :=
  (Nat.eq_zero_of_add_eq_zero h).2

/-! ### sub -/

attribute [simp] Nat.zero_sub Nat.add_sub_cancel succ_sub_succ_eq_sub

theorem succ_sub {m n : Nat} (h : n ≤ m) : succ m - n = succ (m - n) := by
  let ⟨k, hk⟩ := Nat.le.dest h
  rw [← hk, Nat.add_sub_cancel_left, ← add_succ, Nat.add_sub_cancel_left]

protected theorem sub_pos_of_lt (h : m < n) : 0 < n - m :=
  Nat.pos_iff_ne_zero.2 (Nat.sub_ne_zero_of_lt h)

protected theorem sub_le_sub_left (h : n ≤ m) (k : Nat) : k - m ≤ k - n :=
  match m, le.dest h with
  | _, ⟨a, rfl⟩ => by rw [← Nat.sub_sub]; apply sub_le

protected theorem sub_le_sub_right {n m : Nat} (h : n ≤ m) : ∀ k, n - k ≤ m - k
  | 0   => h
  | z+1 => pred_le_pred (Nat.sub_le_sub_right h z)

protected theorem lt_of_sub_ne_zero (h : n - m ≠ 0) : m < n :=
  Nat.not_le.1 (mt Nat.sub_eq_zero_of_le h)

protected theorem sub_ne_zero_iff_lt : n - m ≠ 0 ↔ m < n :=
  ⟨Nat.lt_of_sub_ne_zero, Nat.sub_ne_zero_of_lt⟩

protected theorem lt_of_sub_pos (h : 0 < n - m) : m < n :=
  Nat.lt_of_sub_ne_zero (Nat.pos_iff_ne_zero.1 h)

protected theorem lt_of_sub_eq_succ (h : m - n = succ l) : n < m :=
  Nat.lt_of_sub_pos (h ▸ Nat.zero_lt_succ _)

protected theorem sub_lt_left_of_lt_add {n k m : Nat} (H : n ≤ k) (h : k < n + m) : k - n < m := by
  have := Nat.sub_le_sub_right (succ_le_of_lt h) n
  rwa [Nat.add_sub_cancel_left, Nat.succ_sub H] at this

protected theorem sub_lt_right_of_lt_add {n k m : Nat} (H : n ≤ k) (h : k < m + n) : k - n < m :=
  Nat.sub_lt_left_of_lt_add H (Nat.add_comm .. ▸ h)

protected theorem le_of_sub_eq_zero : ∀ {n m}, n - m = 0 → n ≤ m
  | 0, _, _ => Nat.zero_le ..
  | _+1, _+1, h => Nat.succ_le_succ <| Nat.le_of_sub_eq_zero (Nat.succ_sub_succ .. ▸ h)

protected theorem le_of_sub_le_sub_right : ∀ {n m k : Nat}, k ≤ m → n - k ≤ m - k → n ≤ m
  | 0, _, _, _, _ => Nat.zero_le ..
  | _+1, _, 0, _, h₁ => h₁
  | _+1, _+1, _+1, h₀, h₁ => by
    simp only [Nat.succ_sub_succ] at h₁
    exact succ_le_succ <| Nat.le_of_sub_le_sub_right (le_of_succ_le_succ h₀) h₁

protected theorem sub_le_sub_iff_right {n : Nat} (h : k ≤ m) : n - k ≤ m - k ↔ n ≤ m :=
  ⟨Nat.le_of_sub_le_sub_right h, fun h => Nat.sub_le_sub_right h _⟩

protected theorem sub_eq_iff_eq_add {c : Nat} (h : b ≤ a) : a - b = c ↔ a = c + b :=
  ⟨fun | rfl => by rw [Nat.sub_add_cancel h], fun heq => by rw [heq, Nat.add_sub_cancel]⟩

protected theorem sub_eq_iff_eq_add' {c : Nat} (h : b ≤ a) : a - b = c ↔ a = b + c := by
  rw [Nat.add_comm, Nat.sub_eq_iff_eq_add h]

/-! ### min/max -/

protected theorem min_eq_min (a : Nat) : Nat.min a b = min a b := rfl

protected theorem max_eq_max (a : Nat) : Nat.max a b = max a b := rfl

protected theorem min_comm (a b : Nat) : min a b = min b a := by
  simp [Nat.min_def]; split <;> split <;> try simp [*]
  · next h₁ h₂ => exact Nat.le_antisymm h₁ h₂
  · next h₁ h₂ => cases not_or_intro h₁ h₂ <| Nat.le_total ..

protected theorem min_le_right (a b : Nat) : min a b ≤ b := by rw [Nat.min_def]; split <;> simp [*]

protected theorem min_le_left (a b : Nat) : min a b ≤ a := Nat.min_comm .. ▸ Nat.min_le_right ..

protected theorem min_eq_left {a b : Nat} (h : a ≤ b) : min a b = a := if_pos h

protected theorem min_eq_right {a b : Nat} (h : b ≤ a) : min a b = b := by
  rw [Nat.min_comm]; exact Nat.min_eq_left h

protected theorem max_comm (a b : Nat) : max a b = max b a := by
  simp only [Nat.max_def]
  by_cases h₁ : a ≤ b <;> by_cases h₂ : b ≤ a <;> simp [h₁, h₂]
  · exact Nat.le_antisymm h₂ h₁
  · cases not_or_intro h₁ h₂ <| Nat.le_total ..

protected theorem le_max_left (a b : Nat) : a ≤ max a b := by rw [Nat.max_def]; split <;> simp [*]

protected theorem le_max_right (a b : Nat) : b ≤ max a b := Nat.max_comm .. ▸ Nat.le_max_left ..

protected theorem le_min_of_le_of_le {a b c : Nat} : a ≤ b → a ≤ c → a ≤ min b c := by
  intros; cases Nat.le_total b c with
  | inl h => rw [Nat.min_eq_left h]; assumption
  | inr h => rw [Nat.min_eq_right h]; assumption

protected theorem le_min {a b c : Nat} : a ≤ min b c ↔ a ≤ b ∧ a ≤ c :=
  ⟨fun h => ⟨Nat.le_trans h (Nat.min_le_left ..), Nat.le_trans h (Nat.min_le_right ..)⟩,
   fun ⟨h₁, h₂⟩ => Nat.le_min_of_le_of_le h₁ h₂⟩

protected theorem lt_min {a b c : Nat} : a < min b c ↔ a < b ∧ a < c := Nat.le_min

/-! ### div/mod -/

theorem div_eq_sub_div (h₁ : 0 < b) (h₂ : b ≤ a) : a / b = (a - b) / b + 1 := by
 rw [div_eq a, if_pos]; constructor <;> assumption


theorem mod_add_div (m k : Nat) : m % k + k * (m / k) = m := by
  induction m, k using mod.inductionOn with rw [div_eq, mod_eq]
  | base x y h => simp [h]
  | ind x y h IH => simp [h]; rw [Nat.mul_succ, ← Nat.add_assoc, IH, Nat.sub_add_cancel h.2]

@[simp] protected theorem div_one (n : Nat) : n / 1 = n := by
  have := mod_add_div n 1
  rwa [mod_one, Nat.zero_add, Nat.one_mul] at this

@[simp] protected theorem div_zero (n : Nat) : n / 0 = 0 := by
  rw [div_eq]; simp [Nat.lt_irrefl]

@[simp] protected theorem zero_div (b : Nat) : 0 / b = 0 :=
  (div_eq 0 b).trans <| if_neg <| And.rec Nat.not_le_of_gt

theorem le_div_iff_mul_le (k0 : 0 < k) : x ≤ y / k ↔ x * k ≤ y := by
  induction y, k using mod.inductionOn generalizing x with
    (rw [div_eq]; simp [h]; cases x with | zero => simp [zero_le] | succ x => ?_)
  | base y k h =>
    simp [not_succ_le_zero x, succ_mul, Nat.add_comm]
    refine Nat.lt_of_lt_of_le ?_ (Nat.le_add_right ..)
    exact Nat.not_le.1 fun h' => h ⟨k0, h'⟩
  | ind y k h IH =>
    rw [← add_one, Nat.add_le_add_iff_right, IH k0, succ_mul,
        ← Nat.add_sub_cancel (x*k) k, Nat.sub_le_sub_iff_right h.2, Nat.add_sub_cancel]

theorem div_mul_le_self : ∀ (m n : Nat), m / n * n ≤ m
  | m, 0   => by simp
  | m, n+1 => (le_div_iff_mul_le (Nat.succ_pos _)).1 (Nat.le_refl _)

theorem div_lt_iff_lt_mul (Hk : 0 < k) : x / k < y ↔ x < y * k := by
  rw [← Nat.not_le, ← Nat.not_le]; exact not_congr (le_div_iff_mul_le Hk)

@[simp] theorem add_div_right (x : Nat) {z : Nat} (H : 0 < z) : (x + z) / z = succ (x / z) := by
  rw [div_eq_sub_div H (Nat.le_add_left _ _), Nat.add_sub_cancel]

@[simp] theorem add_div_left (x : Nat) {z : Nat} (H : 0 < z) : (z + x) / z = succ (x / z) := by
  rw [Nat.add_comm, add_div_right x H]

theorem add_mul_div_left (x z : Nat) {y : Nat} (H : 0 < y) : (x + y * z) / y = x / y + z := by
  induction z with
  | zero => rw [Nat.mul_zero, Nat.add_zero, Nat.add_zero]
  | succ z ih => rw [mul_succ, ← Nat.add_assoc, add_div_right _ H, ih]; rfl

theorem add_mul_div_right (x y : Nat) {z : Nat} (H : 0 < z) : (x + y * z) / z = x / z + y := by
  rw [Nat.mul_comm, add_mul_div_left _ _ H]

@[simp] theorem add_mod_right (x z : Nat) : (x + z) % z = x % z := by
  rw [mod_eq_sub_mod (Nat.le_add_left ..), Nat.add_sub_cancel]

@[simp] theorem add_mod_left (x z : Nat) : (x + z) % x = z % x := by
  rw [Nat.add_comm, add_mod_right]

@[simp] theorem add_mul_mod_self_left (x y z : Nat) : (x + y * z) % y = x % y := by
  match z with
  | 0 => rw [Nat.mul_zero, Nat.add_zero]
  | succ z => rw [mul_succ, ← Nat.add_assoc, add_mod_right, add_mul_mod_self_left (z := z)]

@[simp] theorem add_mul_mod_self_right (x y z : Nat) : (x + y * z) % z = x % z := by
  rw [Nat.mul_comm, add_mul_mod_self_left]

@[simp] theorem mul_mod_right (m n : Nat) : (m * n) % m = 0 := by
  rw [← Nat.zero_add (m * n), add_mul_mod_self_left, zero_mod]

@[simp] theorem mul_mod_left (m n : Nat) : (m * n) % n = 0 := by
  rw [Nat.mul_comm, mul_mod_right]

protected theorem div_eq_of_lt_le (lo : k * n ≤ m) (hi : m < succ k * n) : m / n = k :=
have npos : 0 < n := (eq_zero_or_pos _).resolve_left fun hn => by
  rw [hn, Nat.mul_zero] at hi lo; exact absurd lo (Nat.not_le_of_gt hi)
Nat.le_antisymm
  (le_of_lt_succ ((Nat.div_lt_iff_lt_mul npos).2 hi))
  ((Nat.le_div_iff_mul_le npos).2 lo)

theorem sub_mul_div (x n p : Nat) (h₁ : n*p ≤ x) : (x - n*p) / n = x / n - p := by
  match eq_zero_or_pos n with
  | .inl h₀ => rw [h₀, Nat.div_zero, Nat.div_zero, Nat.zero_sub]
  | .inr h₀ => induction p with
    | zero => rw [Nat.mul_zero, Nat.sub_zero, Nat.sub_zero]
    | succ p IH =>
      have h₂ : n * p ≤ x := Nat.le_trans (Nat.mul_le_mul_left _ (le_succ _)) h₁
      have h₃ : x - n * p ≥ n := by
        apply Nat.le_of_add_le_add_right
        rw [Nat.sub_add_cancel h₂, Nat.add_comm]
        rw [mul_succ] at h₁
        exact h₁
      rw [sub_succ, ← IH h₂, div_eq_sub_div h₀ h₃]
      simp [add_one, Nat.pred_succ, mul_succ, Nat.sub_sub]

theorem mul_sub_div (x n p : Nat) (h₁ : x < n*p) : (n * p - succ x) / n = p - succ (x / n) := by
  have npos : 0 < n := (eq_zero_or_pos _).resolve_left fun n0 => by
    rw [n0, Nat.zero_mul] at h₁; exact not_lt_zero _ h₁
  apply Nat.div_eq_of_lt_le
  · rw [Nat.mul_sub_right_distrib, Nat.mul_comm]
    exact Nat.sub_le_sub_left ((div_lt_iff_lt_mul npos).1 (lt_succ_self _)) _
  · show succ (pred (n * p - x)) ≤ (succ (pred (p - x / n))) * n
    rw [succ_pred_eq_of_pos (Nat.sub_pos_of_lt h₁),
      fun h => succ_pred_eq_of_pos (Nat.sub_pos_of_lt h)] -- TODO: why is the function needed?
    · rw [Nat.mul_sub_right_distrib, Nat.mul_comm]
      exact Nat.sub_le_sub_left (div_mul_le_self ..) _
    · rwa [div_lt_iff_lt_mul npos, Nat.mul_comm]

theorem mul_mod_mul_left (z x y : Nat) : (z * x) % (z * y) = z * (x % y) :=
  if y0 : y = 0 then by
    rw [y0, Nat.mul_zero, mod_zero, mod_zero]
  else if z0 : z = 0 then by
    rw [z0, Nat.zero_mul, Nat.zero_mul, Nat.zero_mul, mod_zero]
  else by
    induction x using Nat.strongInductionOn with
    | _ n IH =>
      have y0 : y > 0 := Nat.pos_of_ne_zero y0
      have z0 : z > 0 := Nat.pos_of_ne_zero z0
      cases Nat.lt_or_ge n y with
      | inl yn => rw [mod_eq_of_lt yn, mod_eq_of_lt (Nat.mul_lt_mul_of_pos_left yn z0)]
      | inr yn =>
        rw [mod_eq_sub_mod yn, mod_eq_sub_mod (Nat.mul_le_mul_left z yn),
          ← Nat.mul_sub_left_distrib]
        exact IH _ (sub_lt (Nat.lt_of_lt_of_le y0 yn) y0)

/-! ### pow -/

protected theorem two_pow_pos (w : Nat) : 0 < 2^w := Nat.pos_pow_of_pos _ (by decide)
@[deprecated] alias pow_two_pos := Nat.two_pow_pos -- deprecated 2024-02-09

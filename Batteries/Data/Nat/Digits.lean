/-
Copyright (c) 2025 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: François G. Dorais
-/
import Batteries.Tactic.Basic
import Batteries.Data.Nat.Basic

namespace Nat

/-! # Little-Endian (`LE`) Functions -/

/--
Construct a natural number from a little-endian list of digits in the given base, represented
as elements of `Fin base`:
```
ofDigitsLE (base := 10) [1,2,3] = 321 -- 1*10^0 + 2*10^1 + 3*10^2
ofDigitsLE (base := 2) [0,1,0,0] = 2 -- 0*2^0 + 1*2^1 + 0*2^2 + 0*2^3
ofDigitsLE (base := b) [] = 0 -- any base, including "base 0" and "base 1"
```

All choices for `base` are valid. Since `Fin 0` is empty, there are no valid inputs other than `[]`
in "base 0". For "base 1", the only valid "digit" is zero and therefore:
```
ofDigitsLE (base := 1) l = 0
```
-/
-- Tail-recursive implementation at `ofDigitsLETR`
@[simp] def ofDigitsLE : List (Fin base) → Nat
  | [] => 0
  | d :: l => d + base * ofDigitsLE l

theorem ofDigitsLE_append {l₁ l₂ : List (Fin base)} :
    ofDigitsLE (l₁ ++ l₂) = ofDigitsLE l₁ + ofDigitsLE l₂ * base ^ l₁.length := by
  induction l₁ with
  | nil => simp
  | cons _ _ ih => simp +arith [ih, Nat.mul_add, Nat.mul_left_comm, Nat.pow_add_one']

theorem ofDigitsLE_injective {l₁ l₂ : List (Fin base)} :
    l₁.length = l₂.length → ofDigitsLE l₁ = ofDigitsLE l₂ → l₁ = l₂ := by
  intro hl h
  match l₁, l₂ with
  | [], [] => rfl
  | ⟨n₁, h₁⟩ :: l₁, ⟨n₂, h₂⟩ :: l₂ =>
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hl
    simp only [ofDigitsLE] at h
    simp only [List.cons.injEq]
    constructor
    · congr; calc n₁
        _ = (n₁ + base * ofDigitsLE l₁) % base := by simp [Nat.mod_eq_of_lt h₁]
        _ = (n₂ + base * ofDigitsLE l₂) % base := by rw [h]
        _ = n₂ := by simp [Nat.mod_eq_of_lt h₂]
    · apply ofDigitsLE_injective hl
      calc ofDigitsLE l₁
        _ = ((n₁ + base * ofDigitsLE l₁) / base) := by
          rw [Nat.add_mul_div_left (H := Nat.zero_lt_of_lt h₁), Nat.div_eq_of_lt h₁, Nat.zero_add]
        _ = ((n₂ + base * ofDigitsLE l₂) / base) := by rw [h]
        _ = ofDigitsLE l₂ := by
          rw [Nat.add_mul_div_left (H := Nat.zero_lt_of_lt h₂), Nat.div_eq_of_lt h₂, Nat.zero_add]

/--
Calculates the `prec` least significant digits of `n` in the given `base`. The digits are listed in
little-endian order.

Only "base 0" is invalid, this is ensured by a `NeZero base` instance. In "base 1" the
result is always a list of `0`s with length `prec`.

```
toDigitsUpToLE 123 10 3 = ([3,2,1] : List (Fin 10))
toDigitsUpToLE 2 2 2 = ([0,1] : List (Fin 2))
toDigitsUpToLE 2 2 4 = ([0,1,0,0] : List (Fin 2))
toDigitsUpToLE 12345 1 5 = ([0,0,0,0,0] : List (Fin 1))
```
-/
@[simp] def toDigitsUpToLE (n base prec : Nat) [NeZero base] : List (Fin base) :=
  match prec, n with
  | 0, _ => []
  | prec+1, n => Fin.ofNat base n :: toDigitsUpToLE (n / base) base prec

@[simp]
theorem ofDigitsLE_toDigitsUpToLE [NeZero base] :
    ofDigitsLE (toDigitsUpToLE n base prec) = n % base ^ prec := by
  induction prec generalizing n with
  | zero => simp [Nat.mod_one]
  | succ prec ih => simp [Nat.pow_add_one', Nat.mod_mul, ih]

@[simp]
theorem length_toDigitsUpToLE [NeZero base] :
    (toDigitsUpToLE n base prec).length = prec := by
  induction prec generalizing n with simp [*]

/--
Little-endian list of digits of a natural number `n` in a given `base`. The base must be at
least 2, a tactic attempts to infer this fact from the context but it may need to be provided as
a third argument when the tactic fails.

The most significant digit is guaranteed to be nonzero. When the input number is zero, an empty
list is returned.

```
toDigitsLE 123 10 = ([3,2,1] : List (Fin 10))
toDigitsLE 2 2 = ([0,1] : List (Fin 2))
toDigitsLE 0 12345 = ([] : List (Fin 12345))
```
-/
def toDigitsLE (n base : Nat) (hbase : 2 ≤ base := by omega) : List (Fin base) :=
  if hn : n = 0 then [] else
    have : NeZero base := ⟨by omega⟩
    have _hint : n / base < n := by
      apply Nat.div_lt_of_lt_mul
      rw [Nat.lt_mul_iff_one_lt_left (Nat.zero_lt_of_ne_zero hn)]
      exact hbase
    Fin.ofNat base n :: toDigitsLE (n / base) base

theorem toDigitsLE_zero {h : 2 ≤ base} : toDigitsLE 0 base = [] := by
  rw [toDigitsLE, dif_pos rfl]

theorem toDigitsLE_ne_zero {n : Nat} {h : 2 ≤ base} [NeZero n] :
    have : NeZero base := ⟨by omega⟩ -- TODO: yuck!
    toDigitsLE n base = Fin.ofNat base n :: toDigitsLE (n / base) base := by
  intros; rw [toDigitsLE, dif_neg (NeZero.ne n)]

/-! # Big-Endian (`BE`) Functions -/

/--
Construct a natural number from a big-endian list of digits in the given base, represented
as elements of `Fin base`.

For example:
```
ofDigitsBE (base := 10) [2,3,4] = 234 -- 4*10^0 + 3*10^1 + 2*10^2
ofDigitsBE (base := 2) [0,1,0,0] = 4 -- 0*2^0 + 0*2^1 + 1*2^2 + 0*2^3
ofDigitsBE (base := b) [] = 0 -- any base, including "base 0" and "base 1"
```

There are no valid inputs other than `[]` in "base 0". For "base 1", the only valid "digit" is 0
and therefore:
```
ofDigitsBE (base := 1) l = 0
```
-/
def ofDigitsBE : List (Fin base) → Nat :=
  loop 0
where
  /-- Tail-recursive loop for `ofDigitsBE` -/
  loop
  | n, [] => n
  | n, d :: l => loop (n * base + d) l

private theorem ofDigitsBE.loop_nil :
    loop (base := base) n [] = n := rfl

private theorem ofDigitsBE.loop_cons {l : List (Fin base)} :
    loop n (d :: l) = loop (n * base + d) l := rfl

private theorem ofDigitsBE.loop_eq {l : List (Fin base)} :
    loop n l = n * base ^ l.length + loop 0 l := by
  induction l generalizing n with
  | nil => simp [loop_nil]
  | cons d l ih =>
    simp only [loop_cons, List.length_cons, Nat.zero_mul, Nat.zero_add]
    rw [ih (n := n * base + d), ih (n := d), Nat.add_mul, Nat.add_assoc, Nat.mul_assoc,
      ←Nat.pow_add_one']

@[simp]
theorem ofDigitsBE_nil : ofDigitsBE (base := base) [] = 0 := rfl

@[simp]
theorem ofDigitsBE_cons {l : List (Fin base)} :
    ofDigitsBE (d :: l) = d * base ^ l.length + ofDigitsBE l := by
  simp [ofDigitsBE, ofDigitsBE.loop_cons]
  exact ofDigitsBE.loop_eq ..

theorem ofDigitsBE_append {l₁ l₂ : List (Fin base)} :
    ofDigitsBE (l₁ ++ l₂) = ofDigitsBE l₁ * base ^ l₂.length + ofDigitsBE l₂ := by
  induction l₁ with
  | nil => simp
  | cons d₁ l₁ ih =>
    simp +arith [ih, Nat.add_mul, Nat.pow_add', Nat.mul_assoc]

@[simp]
theorem ofDigitsBE_reverse_eq_ofDigitsLE {l : List (Fin base)} :
    ofDigitsBE l.reverse = ofDigitsLE l := by
  induction l with
  | nil => rfl
  | cons _ _ ih => simp [ofDigitsBE_append, ih, Nat.add_comm, Nat.mul_comm]

@[simp]
theorem ofDigitsLE_reverse_eq_ofDigitsBE {l : List (Fin base)} :
    ofDigitsLE l.reverse = ofDigitsBE l := by
  rw [← List.reverse_reverse l, ofDigitsBE_reverse_eq_ofDigitsLE, List.reverse_reverse]

theorem ofDigitsBE_injective {l₁ l₂ : List (Fin base)} :
    l₁.length = l₂.length → ofDigitsBE l₁ = ofDigitsBE l₂ → l₁ = l₂ := by
  intro hl h
  rw [← List.reverse_inj]
  apply ofDigitsLE_injective
  · simp only [List.length_reverse, hl]
  · simp only [ofDigitsLE_reverse_eq_ofDigitsBE, h]

/-- Tail-recursive implementation of `ofDigitsLE` -/
private abbrev ofDigitsLETR (l : List (Fin base)) : Nat := ofDigitsBE l.reverse

@[csimp]
private theorem ofDigitsLE_eq_ofDigitsLETR : @ofDigitsLE = @ofDigitsLETR := by
  funext; simp [ofDigitsBE_reverse_eq_ofDigitsLE]

/--
Calculates the `prec` least significant digits of `n` in the given `base`. The digits are listed in
big-endian order.
-/
def toDigitsUpToBE (n base prec : Nat) [NeZero base] : List (Fin base) :=
  loop prec n []
where
  /-- Tail-recursive loop for `toDigitsUpToBE` -/
  loop : Nat → Nat → List (Fin base) → List (Fin base)
  | 0, _, l => l
  | prec+1, n, l => loop prec (n / base) (Fin.ofNat base n :: l)

private theorem toDigitsUpToBE.loop_zero [NeZero base] :
    loop base 0 n l = l := rfl

private theorem toDigitsUpToBE.loop_succ [NeZero base] :
    loop base (prec+1) n l = loop base prec (n / base) (Fin.ofNat base n :: l) := rfl

private theorem toDigitsUpToBE.loop_eq [NeZero base] :
    loop base prec n l = loop base prec n [] ++ l := by
  induction prec generalizing n l with simp only [loop_zero, loop_succ, List.nil_append]
  | succ prec ih =>
    conv => rhs; rw [ih, List.append_assoc]
    rw [ih]; rfl

private theorem toDigitsUpToBE.ofDigitsBE_loop [NeZero base] :
    ofDigitsBE (loop base prec n l) = (n % base ^ prec) * base ^ l.length + ofDigitsBE l := by
  induction prec generalizing n l with
  | zero => simp [loop, Nat.mod_one]
  | succ prec ih =>
    simp +arith only [loop, ih, List.length, ofDigitsBE_cons, Fin.val_ofNat]
    rw [Nat.pow_add_one', ← Nat.mul_assoc, ← Nat.add_mul, Nat.pow_add_one', Nat.mod_mul,
      Nat.mul_comm base]

@[simp]
theorem toDigitsUpToBE_zero [NeZero base] :
    toDigitsUpToBE n base 0 = [] := rfl

@[simp]
theorem toDigitsUpToBE_succ [NeZero base] :
    toDigitsUpToBE n base (prec+1) = toDigitsUpToBE (n / base) base prec ++ [Fin.ofNat base n] := by
  simp [toDigitsUpToBE, toDigitsUpToBE.loop_succ]; rw [toDigitsUpToBE.loop_eq]

@[simp]
theorem ofDigitsBE_toDigitsUpToBE [NeZero base] :
    ofDigitsBE (toDigitsUpToBE n base prec) = n % base ^ prec := by
  simp [toDigitsUpToBE, toDigitsUpToBE.ofDigitsBE_loop]

@[simp]
theorem length_toDigitsUpToBE [NeZero base] :
    (toDigitsUpToBE n base prec).length = prec := by
  induction prec generalizing n with simp [*]

@[simp]
theorem reverse_toDigitsUpToBE_eq_toDigitsUpToLE [NeZero base] :
    (toDigitsUpToBE n base prec).reverse = toDigitsUpToLE n base prec := by
  apply ofDigitsLE_injective <;> simp

@[simp]
theorem reverse_toDigitsUpToLE_eq_toDigitsUpToBE [NeZero base] :
    (toDigitsUpToLE n base prec).reverse = toDigitsUpToBE n base prec := by
  apply ofDigitsBE_injective <;> simp

/--
Big-endian list of digits of a natural number `n` in a given `base`. The base must be at least 2,
a tactic attempts to infer this fact from the context but it may need to be provided as a third
argument when the tactic fails.

When the input number is zero, an empty list is returned. Otherwise, the most significant digit is
guaranteed to be nonzero.

```
toDigitsBE 123 10 = ([1,2,3] : List (Fin 10))
toDigitsBE 2 2 = ([1,0] : List (Fin 2))
toDigitsBE 0 12345 = ([] : List (Fin 12345))
```
-/
def toDigitsBE (n base : Nat) (hbase : 2 ≤ base := by omega) : List (Fin base) :=
  loop 0 base n [] <| by rw [Nat.pow_zero, Nat.pow_one]
where
  /-- Tail-recursive loop for `toDigitsBE`. -/
  loop (p b n : Nat) (l : List (Fin base)) (hb : base ^ (2 ^ p) = b) :=
    if hn : n = 0 then l else
      have : NeZero base := ⟨by omega⟩
      let q := n / b
      let r := n % b
      if hq : q ≠ 0 then
        have : 2 ≤ b := Nat.le_trans hbase <| by
          rw [← hb]; exact Nat.le_pow (Nat.two_pow_pos _)
        have : q < n := Nat.div_lt_self (by omega) (by omega)
        loop (p+1) (b * b) q (toDigitsUpToBE r base (2 ^ p) ++ l) <| by
          rw [Nat.pow_add_one, Nat.mul_two, Nat.pow_add, hb]
      else
        have : n / base < n := Nat.div_lt_self (by omega) (by omega)
        loop 0 base (n / base) (Fin.ofNat base n :: l) <| by
          rw [Nat.pow_zero, Nat.pow_one]

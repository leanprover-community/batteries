/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad, Mario Carneiro
-/
import Std.Classes.Dvd

namespace Nat

/--
  Recursor identical to `Nat.rec` but uses notations `0` for `Nat.zero` and `·+1` for `Nat.succ`
-/
@[elab_as_elim]
protected def recAux {motive : Nat → Sort _}
    (zero : motive 0) (succ : ∀ n, motive n → motive (n+1)) : (t : Nat) → motive t
  | 0 => zero
  | _+1 => succ _ (Nat.recAux zero succ _)

/--
  Recursor identical to `Nat.recOn` but uses notations `0` for `Nat.zero` and `·+1` for `Nat.succ`
-/
@[elab_as_elim]
protected def recAuxOn {motive : Nat → Sort _} (t : Nat) (zero : motive 0)
  (succ : ∀ n, motive n → motive (n+1)) : motive t := Nat.recAux zero succ t

/--
  Recursor identical to `Nat.casesOn` but uses notations `0` for `Nat.zero` and `·+1` for `Nat.succ`
-/
@[elab_as_elim]
protected def casesAuxOn {motive : Nat → Sort _} (t : Nat) (zero : motive 0)
  (succ : ∀ n, motive (n+1)) : motive t := Nat.recAux zero (fun n _ => succ n) t

/--
  Strong recursor for `Nat`
-/
@[elab_as_elim]
protected def strongRec {motive : Nat → Sort _} (ind : ∀ n, (∀ m, m < n → motive m) → motive n)
  (t : Nat) : motive t := ind t fun m _ => Nat.strongRec ind m

/--
  Strong recursor for `Nat`
-/
@[elab_as_elim]
protected def strongRecOn (t : Nat) {motive : Nat → Sort _}
  (ind : ∀ n, (∀ m, m < n → motive m) → motive n) : motive t := Nat.strongRec ind t

/--
  Simple diagonal recursor for `Nat`
-/
@[elab_as_elim]
protected def recDiagAux {motive : Nat → Nat → Sort _}
  (zero_left : ∀ n, motive 0 n)
  (zero_right : ∀ m, motive m 0)
  (succ_succ : ∀ m n, motive m n → motive (m+1) (n+1)) :
    (m n : Nat) → motive m n
  | 0, _ => zero_left _
  | _, 0 => zero_right _
  | _+1, _+1 => succ_succ _ _ (Nat.recDiagAux zero_left zero_right succ_succ _ _)

/--
  Diagonal recursor for `Nat`
-/
@[elab_as_elim]
protected def recDiag {motive : Nat → Nat → Sort _}
  (zero_zero : motive 0 0)
  (zero_succ : ∀ n, motive 0 n → motive 0 (n+1))
  (succ_zero : ∀ m, motive m 0 → motive (m+1) 0)
  (succ_succ : ∀ m n, motive m n → motive (m+1) (n+1)) :
    (m n : Nat) → motive m n := Nat.recDiagAux left right succ_succ
where
  /-- Left leg for `Nat.recDiag` -/
  left : ∀ n, motive 0 n
  | 0 => zero_zero
  | _+1 => zero_succ _ (left _)
  /-- Right leg for `Nat.recDiag` -/
  right : ∀ m, motive m 0
  | 0 => zero_zero
  | _+1 => succ_zero _ (right _)

/--
  Diagonal recursor for `Nat`
-/
@[elab_as_elim]
protected def recDiagOn {motive : Nat → Nat → Sort _} (m n : Nat)
  (zero_zero : motive 0 0)
  (zero_succ : ∀ n, motive 0 n → motive 0 (n+1))
  (succ_zero : ∀ m, motive m 0 → motive (m+1) 0)
  (succ_succ : ∀ m n, motive m n → motive (m+1) (n+1)) :
    motive m n := Nat.recDiag zero_zero zero_succ succ_zero succ_succ m n

/--
  Diagonal recursor for `Nat`
-/
@[elab_as_elim]
protected def casesDiagOn {motive : Nat → Nat → Sort _} (m n : Nat)
  (zero_zero : motive 0 0)
  (zero_succ : ∀ n, motive 0 (n+1))
  (succ_zero : ∀ m, motive (m+1) 0)
  (succ_succ : ∀ m n, motive (m+1) (n+1)) :
    motive m n :=
  Nat.recDiag zero_zero (fun _ _ => zero_succ _) (fun _ _ => succ_zero _)
    (fun _ _ _ => succ_succ _ _) m n

/--
Divisibility of natural numbers. `a ∣ b` (typed as `\|`) says that
there is some `c` such that `b = a * c`.
-/
instance : Dvd Nat := ⟨fun a b => ∃ c, b = a * c⟩

/-- Sum of a list of natural numbers. -/
protected def sum (l : List Nat) : Nat := l.foldr (·+·) 0

/--
Integer square root function. Implemented via Newton's method.
-/
def sqrt (n : Nat) : Nat :=
  if n ≤ 1 then n else
  iter n (n / 2)
where
  /-- Auxiliary for `sqrt`. If `guess` is greater than the integer square root of `n`,
  returns the integer square root of `n`. -/
  iter (n guess : Nat) : Nat :=
    let next := (guess + n / guess) / 2
    if _h : next < guess then
      iter n next
    else
      guess
termination_by iter guess => guess

/-- `bodd n` returns `true` if `n` is odd-/
def bodd (n : Nat) : Bool :=
  (1 &&& n) != 0

/-- `div2 n = ⌊n/2⌋` the greatest integer smaller than `n/2`-/
def div2 (n : Nat) : Nat :=
  n >>> 1

/-- `bit b` appends the digit `b` to the binary representation of
  its natural number input. -/
def bit (b : Bool) (n : Nat) : Nat :=
  cond b (n + n + 1) (n + n)

/-!
### testBit
We define an operation for testing individual bits in the binary representation
of a number.
-/

/-- `testBit m n` returns whether the `(n+1)ˢᵗ` least significant bit is `1` or `0`-/
def testBit (m n : Nat) : Bool :=
  bodd (m >>> n)

theorem bit_val (b n) : bit b n = 2 * n + cond b 1 0 := by
  cases b <;> rw [Nat.mul_comm]
  · exact congrArg (· + n) n.zero_add.symm
  · exact congrArg (· + n + 1) n.zero_add.symm

theorem div2_val (n) : div2 n = n / 2 := rfl

theorem mod_two_eq_zero_or_one (n : Nat) : n % 2 = 0 ∨ n % 2 = 1 :=
  match n % 2, @Nat.mod_lt n 2 (by decide) with
  | 0, _ => .inl rfl
  | 1, _ => .inr rfl

theorem mod_two_of_bodd (n : Nat) : n % 2 = cond (bodd n) 1 0 := by
  dsimp [bodd, (· &&& ·), AndOp.and, land]
  unfold bitwise
  by_cases n0 : n = 0
  · simp [n0]
  · simp only [ite_false, decide_True, Bool.true_and, decide_eq_true_eq, n0,
      show 1 / 2 = 0 by decide]
    cases mod_two_eq_zero_or_one n with | _ h => simp [h]; rfl

theorem bodd_add_div2 (n : Nat) : 2 * div2 n + cond (bodd n) 1 0 = n := by
  rw [← mod_two_of_bodd, div2_val, Nat.div_add_mod]

theorem bit_decomp (n : Nat) : bit (bodd n) (div2 n) = n :=
  (bit_val _ _).trans (bodd_add_div2 _)

theorem bit_eq_zero_iff {n : Nat} {b : Bool} : bit b n = 0 ↔ n = 0 ∧ b = false := by
  cases n <;> cases b <;> simp [bit, Nat.succ_add]

/-- For a predicate `C : Nat → Sort u`, if instances can be
  constructed for natural numbers of the form `bit b n`,
  they can be constructed for any given natural number. -/
@[inline]
def bitCasesOn {C : Nat → Sort u} (n) (h : ∀ b n, C (bit b n)) : C n := bit_decomp n ▸ h _ _

theorem binaryRec_decreasing (h : n ≠ 0) : div2 n < n :=
  div_lt_self (n.zero_lt_of_ne_zero h) (by decide)

/-- A recursion principle for `bit` representations of natural numbers.
  For a predicate `C : Nat → Sort u`, if instances can be
  constructed for natural numbers of the form `bit b n`,
  they can be constructed for all natural numbers. -/
@[specialize]
def binaryRec {C : Nat → Sort u} (z : C 0) (f : ∀ b n, C n → C (bit b n)) (n : Nat) : C n :=
  if n0 : n = 0 then by rw [n0]; exact z
  else by rw [← n.bit_decomp]; exact f n.bodd n.div2 (binaryRec z f n.div2)
  decreasing_by exact binaryRec_decreasing n0

/-- The same as `binaryRec`, but the induction step can assume that if `n=0`,
  the bit being appended is `true`-/
@[elab_as_elim, specialize]
def binaryRec' {C : Nat → Sort u} (z : C 0)
    (f : ∀ b n, (n = 0 → b = true) → C n → C (bit b n)) : ∀ n, C n :=
  binaryRec z fun b n ih =>
    if h : n = 0 → b = true then f b n h ih
    else by
      have : bit b n = 0 := by
        rw [bit_eq_zero_iff]
        cases n <;> cases b <;> simp at h <;> simp [h]
      exact this ▸ z

/-- The same as `binaryRec`, but special casing both 0 and 1 as base cases -/
@[elab_as_elim, specialize]
def binaryRecFromOne {C : Nat → Sort u} (z₀ : C 0) (z₁ : C 1)
    (f : ∀ b n, n ≠ 0 → C n → C (bit b n)) : ∀ n, C n :=
  binaryRec' z₀ fun b n h ih =>
    if h' : n = 0 then by
      rw [h', h h']
      exact z₁
    else f b n h' ih

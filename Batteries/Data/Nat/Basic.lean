/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad, Mario Carneiro
-/

namespace Nat


/--
  Recursor identical to `Nat.recOn` but uses notations `0` for `Nat.zero` and `·+1` for `Nat.succ`
-/
@[elab_as_elim]
protected def recAuxOn {motive : Nat → Sort _} (t : Nat) (zero : motive 0)
  (succ : ∀ n, motive n → motive (n+1)) : motive t := Nat.recAux zero succ t

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
  Strong recursor via a `Nat`-valued measure
-/
@[elab_as_elim]
def strongRecMeasure (f : α → Nat) {motive : α → Sort _}
    (ind : ∀ x, (∀ y, f y < f x → motive y) → motive x) (x : α) : motive x :=
  ind x fun y _ => strongRecMeasure f ind y
termination_by f x

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
  termination_by guess

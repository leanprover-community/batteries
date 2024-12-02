/-
Copyright (c) 2017 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis, Keeley Hoek, Mario Carneiro
-/
import Batteries.Tactic.Alias
import Batteries.Data.Array.Basic
import Batteries.Data.List.Basic

namespace Fin

/-- `min n m` as an element of `Fin (m + 1)` -/
def clamp (n m : Nat) : Fin (m + 1) := ⟨min n m, Nat.lt_succ_of_le (Nat.min_le_right ..)⟩

@[deprecated (since := "2024-11-15")]
alias enum := Array.finRange

@[deprecated (since := "2024-11-15")]
alias list := List.finRange

/-- Sum of a list indexed by `Fin n`. -/
protected def sum [OfNat α (nat_lit 0)] [Add α] (x : Fin n → α) : α :=
  foldr n (x · + ·) 0

/-- Product of a list indexed by `Fin n`. -/
protected def prod [OfNat α (nat_lit 1)] [Mul α] (x : Fin n → α) : α :=
  foldr n (x · * ·) 1

/-- Count the number of true values of a decidable predicate on `Fin n`. -/
protected def count (P : Fin n → Prop) [DecidablePred P] : Nat :=
  Fin.sum (if P · then 1 else 0)

/-- Find the first true value of a decidable predicate on `Fin n`, if there is one. -/
protected def find? (P : Fin n → Prop) [DecidablePred P] : Option (Fin n) :=
  foldr n (fun i v => if P i then some i else v) none

/-- Custom recursor for `Fin (n+1)`. -/
def recZeroSuccOn {motive : Fin (n+1) → Sort _} (x : Fin (n+1))
    (zero : motive 0) (succ : (x : Fin n) → motive x.castSucc → motive x.succ) : motive x :=
  match x with
  | 0 => zero
  | ⟨x+1, hx⟩ =>
    let x : Fin n := ⟨x, Nat.lt_of_succ_lt_succ hx⟩
    succ x <| recZeroSuccOn x.castSucc zero succ

/-- Custom recursor for `Fin (n+1)`. -/
def casesZeroSuccOn {motive : Fin (n+1) → Sort _} (x : Fin (n+1))
    (zero : motive 0) (succ : (x : Fin n) → motive x.succ) : motive x :=
  match x with
  | 0 => zero
  | ⟨x+1, hx⟩ => succ ⟨x, Nat.lt_of_succ_lt_succ hx⟩

/-
Copyright (c) 2017 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis, Keeley Hoek, Mario Carneiro
-/
import Std.Data.Nat.Init.Lemmas

namespace Fin

protected theorem pos (i : Fin n) : 0 < n :=
  Nat.lt_of_le_of_lt (Nat.zero_le _) i.2

/-- The greatest value of `Fin (n+1)`. -/
@[inline] def last (n : Nat) : Fin (n + 1) := ⟨n, n.lt_succ_self⟩

/-- `castLT i h` embeds `i` into a `Fin` where `h` proves it belongs into.  -/
@[inline] def castLT (i : Fin m) (h : i.1 < n) : Fin n := ⟨i.1, h⟩

/-- `castLE h i` embeds `i` into a larger `Fin` type.  -/
@[inline] def castLE (h : n ≤ m) (i : Fin n) : Fin m := ⟨i, Nat.lt_of_lt_of_le i.2 h⟩

/-- `cast eq i` embeds `i` into an equal `Fin` type. -/
@[inline] def cast (eq : n = m) (i : Fin n) : Fin m := ⟨i, eq ▸ i.2⟩

/-- `castAdd m i` embeds `i : Fin n` in `Fin (n+m)`. See also `Fin.natAdd` and `Fin.addNat`. -/
@[inline] def castAdd (m) : Fin n → Fin (n + m) :=
  castLE <| Nat.le_add_right n m

/-- `castSucc i` embeds `i : Fin n` in `Fin (n+1)`. -/
@[inline] def castSucc : Fin n → Fin (n + 1) := castAdd 1

/-- `addNat m i` adds `m` to `i`, generalizes `Fin.succ`. -/
def addNat (i : Fin n) (m) : Fin (n + m) := ⟨i + m, Nat.add_lt_add_right i.2 _⟩

/-- `natAdd n i` adds `n` to `i` "on the left". -/
def natAdd (n) (i : Fin m) : Fin (n + m) := ⟨n + i, Nat.add_lt_add_left i.2 _⟩

/-- Maps `0` to `n-1`, `1` to `n-2`, ..., `n-1` to `0`. -/
@[inline] def rev (i : Fin n) : Fin n := ⟨n - (i + 1), Nat.sub_lt i.pos (Nat.succ_pos _)⟩

/-- `subNat i h` subtracts `m` from `i`, generalizes `Fin.pred`. -/
@[inline] def subNat (m) (i : Fin (n + m)) (h : m ≤ i) : Fin n :=
  ⟨i - m, Nat.sub_lt_right_of_lt_add h i.2⟩

/-- Predecessor of a nonzero element of `Fin (n+1)`. -/
@[inline] def pred {n : Nat} (i : Fin (n + 1)) (h : i.1 ≠ 0) : Fin n :=
  subNat 1 i (Nat.pos_of_ne_zero h)

/-- `succAbove p i` embeds `Fin n` into `Fin (n + 1)` with a hole around `p`. -/
def succAbove (p : Fin (n + 1)) (i : Fin n) : Fin (n + 1) :=
  if i.1 < p.1 then castSucc i else succ i

/-- `predAbove p i` embeds `i : Fin (n+1)` into `Fin n` by subtracting one if `p < i`. -/
def predAbove (p : Fin n) (i : Fin (n + 1)) : Fin n :=
  if h : castSucc p < i then i.pred (Nat.not_eq_zero_of_lt h)
  else i.castLT (Nat.lt_of_le_of_lt (Nat.ge_of_not_lt h) p.2)

/-- `castPred` embeds `i : Fin (n + 2)` into `Fin (n + 1)`
by lowering just `last (n + 1)` to `last n`. -/
def castPred (i : Fin (n + 2)) : Fin (n + 1) := predAbove (last n) i

/-- `min n m` as an element of `Fin (m + 1)` -/
def clamp (n m : Nat) : Fin (m + 1) := ⟨min n m, Nat.lt_succ_of_le (Nat.min_le_right ..)⟩

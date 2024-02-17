/-
Copyright (c) 2017 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis, Keeley Hoek, Mario Carneiro
-/
import Std.Data.Nat.Init.Lemmas

namespace Fin

instance : OfNat (Fin ((n+1)^k)) i :=
  ⟨Fin.ofNat' i (Nat.pos_pow_of_pos k (Nat.succ_pos n))⟩

protected theorem pos (i : Fin n) : 0 < n :=
  Nat.lt_of_le_of_lt (Nat.zero_le _) i.2

/-- The greatest value of `Fin (n+1)`. -/
@[inline] def last (n : Nat) : Fin (n + 1) := ⟨n, n.lt_succ_self⟩

/-- The greatest value of `Fin ((n+1)^k)`. -/
@[inline] def powLast (n k : Nat) : Fin ((n + 1)^k) :=
  ⟨(n+1)^k - 1, Nat.pred_lt (Nat.ne_of_gt (Nat.pos_pow_of_pos k (Nat.succ_pos n)))⟩

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
@[inline] def pred {n : Nat} (i : Fin (n + 1)) (h : i ≠ 0) : Fin n :=
  subNat 1 i <| Nat.pos_of_ne_zero <| mt (Fin.eq_of_val_eq (j := 0)) h

/-- `min n m` as an element of `Fin (m + 1)` -/
def clamp (n m : Nat) : Fin (m + 1) := ⟨min n m, Nat.lt_succ_of_le (Nat.min_le_right ..)⟩

/-- Folds over `Fin n` from the left: `foldl 3 f x = f (f (f x 0) 1) 2`. -/
@[inline] def foldl (n) (f : α → Fin n → α) (init : α) : α := loop init 0 where
  /-- Inner loop for `Fin.foldl`. `Fin.foldl.loop n f x i = f (f (f x i) ...) (n-1)`  -/
  loop (x : α) (i : Nat) : α :=
    if h : i < n then loop (f x ⟨i, h⟩) (i+1) else x
  termination_by n - i

/-- Folds over `Fin n` from the right: `foldr 3 f x = f 0 (f 1 (f 2 x))`. -/
@[inline] def foldr (n) (f : Fin n → α → α) (init : α) : α := loop ⟨n, Nat.le_refl n⟩ init where
  /-- Inner loop for `Fin.foldr`. `Fin.foldr.loop n f i x = f 0 (f ... (f (i-1) x))`  -/
  loop : {i // i ≤ n} → α → α
  | ⟨0, _⟩, x => x
  | ⟨i+1, h⟩, x => loop ⟨i, Nat.le_of_lt h⟩ (f ⟨i, h⟩ x)

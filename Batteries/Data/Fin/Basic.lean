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

/-- Dependent version of `Fin.foldlM`. -/
@[inline] def dfoldlM [Monad m] (n : Nat) (α : Fin (n + 1) → Sort _)
    (f : ∀ (i : Fin n), α i.castSucc → m (α i.succ)) (init : α 0) : m (α (last n)) :=
  loop 0 (Nat.zero_lt_succ n) init where
  /-- Inner loop for `Fin.dfoldlM`.
    ```
  Fin.foldM.loop n α f i h xᵢ = do
    let xᵢ₊₁ ← f i xᵢ
    ...
    let xₙ ← f (n-1) xₙ₋₁
    pure xₙ
  ```
  -/
  @[semireducible] loop (i : Nat) (h : i < n + 1) (x : α ⟨i, h⟩) : m (α (last n)) :=
    if h' : i < n then
      (f ⟨i, h'⟩ x) >>= loop (i + 1) (Nat.succ_lt_succ h')
    else
      haveI : ⟨i, h⟩ = last n := by ext; simp; omega
      _root_.cast (congrArg (fun i => m (α i)) this) (pure x)

/-- Dependent version of `Fin.foldrM`. -/
@[inline] def dfoldrM [Monad m] (n : Nat) (α : Fin (n + 1) → Sort _)
    (f : ∀ (i : Fin n), α i.succ → m (α i.castSucc)) (init : α (last n)) : m (α 0) :=
  loop n (Nat.lt_succ_self n) init where
  /-- Inner loop for `Fin.foldRevM`.
    ```
  Fin.foldRevM.loop n α f i h xᵢ = do
    let xᵢ₋₁ ← f (i+1) xᵢ
    ...
    let x₁ ← f 1 x₂
    let x₀ ← f 0 x₁
    pure x₀
  ```
  -/
  @[semireducible] loop (i : Nat) (h : i < n + 1) (x : α ⟨i, h⟩) : m (α 0) :=
    if h' : i > 0 then
      (f ⟨i - 1, by omega⟩ (by simpa [Nat.sub_one_add_one_eq_of_pos h'] using x))
        >>= loop (i - 1) (by omega)
    else
      haveI : ⟨i, h⟩ = 0 := by ext; simp; omega
      _root_.cast (congrArg (fun i => m (α i)) this) (pure x)

/-- Dependent version of `Fin.foldl`. -/
@[inline] def dfoldl (n : Nat) (α : Fin (n + 1) → Sort _)
    (f : ∀ (i : Fin n), α i.castSucc → α i.succ) (init : α 0) : α (last n) :=
  loop 0 (Nat.zero_lt_succ n) init where
  /-- Inner loop for `Fin.dfoldl`. `Fin.dfoldl.loop n α f i h x = f n (f (n-1) (... (f i x)))` -/
  @[semireducible, specialize] loop (i : Nat) (h : i < n + 1) (x : α ⟨i, h⟩) : α (last n) :=
    if h' : i < n then
      loop (i + 1) (Nat.succ_lt_succ h') (f ⟨i, h'⟩ x)
    else
      haveI : ⟨i, h⟩ = last n := by ext; simp; omega
      _root_.cast (congrArg α this) x

/-- Dependent version of `Fin.foldr`. -/
@[inline] def dfoldr (n : Nat) (α : Fin (n + 1) → Sort _)
    (f : ∀ (i : Fin n), α i.succ → α i.castSucc) (init : α (last n)) : α 0 :=
  loop n (Nat.lt_succ_self n) init where
  /-- Inner loop for `Fin.dfoldr`.
    `Fin.dfoldr.loop n α f i h x = f 0 (f 1 (... (f i x)))`  -/
  @[specialize] loop (i : Nat) (h : i < n + 1) (x : α ⟨i, h⟩) : α 0 :=
    match i with
    | i + 1 => loop i (Nat.lt_of_succ_lt h) (f ⟨i, Nat.lt_of_succ_lt_succ h⟩ x)
    | 0 => x

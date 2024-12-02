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

/--
Folds a monadic function over `Fin n` from left to right:
```
Fin.foldlM n f x₀ = do
  let x₁ ← f x₀ 0
  let x₂ ← f x₁ 1
  ...
  let xₙ ← f xₙ₋₁ (n-1)
  pure xₙ
```
-/
@[inline] def foldlM [Monad m] (n) (f : α → Fin n → m α) (init : α) : m α := loop init 0 where
  /--
  Inner loop for `Fin.foldlM`.
  ```
  Fin.foldlM.loop n f xᵢ i = do
    let xᵢ₊₁ ← f xᵢ i
    ...
    let xₙ ← f xₙ₋₁ (n-1)
    pure xₙ
  ```
  -/
  loop (x : α) (i : Nat) : m α := do
    if h : i < n then f x ⟨i, h⟩ >>= (loop · (i+1)) else pure x
  termination_by n - i

/--
Folds a monadic function over `Fin n` from right to left:
```
Fin.foldrM n f xₙ = do
  let xₙ₋₁ ← f (n-1) xₙ
  let xₙ₋₂ ← f (n-2) xₙ₋₁
  ...
  let x₀ ← f 0 x₁
  pure x₀
```
-/
@[inline] def foldrM [Monad m] (n) (f : Fin n → α → m α) (init : α) : m α :=
  loop ⟨n, Nat.le_refl n⟩ init where
  /--
  Inner loop for `Fin.foldrM`.
  ```
  Fin.foldrM.loop n f i xᵢ = do
    let xᵢ₋₁ ← f (i-1) xᵢ
    ...
    let x₁ ← f 1 x₂
    let x₀ ← f 0 x₁
    pure x₀
  ```
  -/
  loop : {i // i ≤ n} → α → m α
  | ⟨0, _⟩, x => pure x
  | ⟨i+1, h⟩, x => f ⟨i, h⟩ x >>= loop ⟨i, Nat.le_of_lt h⟩

variable (n : Nat) (α : Fin (n + 1) → Sort _)

/-- Dependent version of `Fin.foldl`. -/
def fold (f : ∀ (i : Fin n), α i.castSucc → α i.succ) (init : α 0) : α (last n) :=
  loop 0 (Nat.zero_lt_succ n) init where
  /-- Inner loop for `Fin.fold`. `Fin.fold.loop n α f i h x = f n (f (n-1) (... (f i x)))`  -/
  loop (i : Nat) (h : i < n + 1) (x : α ⟨i, h⟩) : α (last n) :=
    if h' : i < n then
      loop (i + 1) (Nat.succ_lt_succ h') (f ⟨i, h'⟩ x)
    else
      haveI : ⟨i, h⟩ = last n := by ext; simp; omega
      _root_.cast (congrArg α this) x

/-- Dependent version of `Fin.foldr`. -/
def foldRev (f : ∀ (i : Fin n), α i.succ → α i.castSucc) (init : α (last n)) : α 0 :=
  loop n (Nat.lt_succ_self n) init where
  /-- Inner loop for `Fin.foldRev`.
    `Fin.foldRev.loop n α f i h x = f 0 (f 1 (... (f i x)))`  -/
  loop (i : Nat) (h : i < n + 1) (x : α ⟨i, h⟩) : α 0 :=
    if h' : i > 0 then
      loop (i - 1) (by omega) (f ⟨i - 1, by omega⟩
        (by simpa [Nat.sub_one_add_one_eq_of_pos h'] using x))
    else
      haveI : ⟨i, h⟩ = 0 := by ext; simp; omega
      _root_.cast (congrArg α this) x

/-- Dependent version of `Fin.foldlM`. -/
def foldM [Monad m] (f : ∀ (i : Fin n), α i.castSucc → m (α i.succ)) (init : α 0)
    : m (α (last n)) := loop 0 (Nat.zero_lt_succ n) init where
  /-- Inner loop for `Fin.foldM`.
    ```
  Fin.foldM.loop n α f i h xᵢ = do
    let xᵢ₊₁ ← f i xᵢ
    ...
    let xₙ ← f (n-1) xₙ₋₁
    pure xₙ
  ```
  -/
  loop (i : Nat) (h : i < n + 1) (x : α ⟨i, h⟩) : m (α (last n)) :=
    if h' : i < n then
      (f ⟨i, h'⟩ x) >>= loop (i + 1) (Nat.succ_lt_succ h')
    else
      haveI : ⟨i, h⟩ = last n := by ext; simp; omega
      _root_.cast (congrArg (fun i => m (α i)) this) (pure x)
  termination_by n - i

/-- Dependent version of `Fin.foldrM`. -/
def foldRevM [Monad m] (f : ∀ (i : Fin n), α i.succ → m (α i.castSucc)) (init : α (last n))
    : m (α 0) := loop n (Nat.lt_succ_self n) init where
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
  loop (i : Nat) (h : i < n + 1) (x : α ⟨i, h⟩) : m (α 0) :=
    if h' : i > 0 then
      (f ⟨i - 1, by omega⟩ (by simpa [Nat.sub_one_add_one_eq_of_pos h'] using x))
        >>= loop (i - 1) (by omega)
    else
      haveI : ⟨i, h⟩ = 0 := by ext; simp; omega
      _root_.cast (congrArg (fun i => m (α i)) this) (pure x)
